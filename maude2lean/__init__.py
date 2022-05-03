#
# Transform a Maude module into a Lean specification
#

import importlib.resources as pkg_resources
import sys
from collections import Counter
from itertools import chain

import maude

from . import data
from .graph import Graph
from .lean import LeanWriter
from .maudext import MetalevelUtil, get_variables_stmt


def subindex(n: int):
	"""Numerical subindex using Unicode characters"""

	zero = ord('₀')
	sub = chr(zero + (n % 10))

	while n >= 10:
		n /= 10
		sub = chr(zero + (n % 10)) + sub

	return sub


def make_variables(prefix: str, count: int):
	"""Generate the given number of fresh variables"""

	if count == 1:  # Single variables do not take subindices
		return prefix,

	return tuple(f'{prefix}{subindex(i)}' for i in range(count))


def replace(iterable, index: int, elem):
	"""Replace the index-th element of an iterable by the given one"""

	return ((e if k != index else elem) for k, e in enumerate(iterable))


class Maude2Lean:
	"""Maude to Lean translation"""

	# Lean identifiers do not admit symbols in general, so this table
	# includes replacements for some of the most frequent ones (still,
	# renamings can be defined by the user)
	ID_REPLACE_MAP = {
		'_': '',
		'*': 'mul',
		'+': 'sum',
		'-': 'sub',
		'^': 'pow',
		'0': 'zero',
		'<': 'lt',
		'>': 'gt',
		'=': 'eq',
		'&': 'amp',
		'|': 'bar',
		'[': 'lbrak',
		']': 'rbrack',
		'/': 'slash',
		'\\': 'bslash',
		':': 'colon',
		';': 'scolon',
	}

	def __init__(self, module: maude.Module, opts: dict):
		self.mod = module  # Module we are translating
		self.opts = opts  # User options

		self.mlu = MetalevelUtil()

		# Relation names
		self.has_sort = '.has_sort '
		self.eqa = '.eqa '
		self.eqe = '.eqe '
		self.rw_one = '.rw_one '
		self.rw_star = '.rw_star '

		use_notation = opts.get('use-notation', ())

		if 'eqa' in use_notation:
			self.eqa = ' ' + opts.get('eqa-symbol', '=A') + ' '

		if 'eqe' in use_notation:
			self.eqe = ' ' + opts.get('eqe-symbol', '=E') + ' '

		if 'has_sort' in use_notation:
			self.has_sort = ' ' + opts.get('has-sort-symbol', '⊳') + ' '

		if 'rw_one' in use_notation:
			self.rw_one = ' ' + opts.get('rw-one-symbol', '=>1') + ' '

		if 'rw_star' in use_notation:
			self.rw_star = ' ' + opts.get('rw-star-symbol', '=>*') + ' '

		# Implicit membership axiom labels (per kind)
		self.impl_mb_axioms = {}

		self._index_module()

	@staticmethod
	def _allowed_identifier(name: str):
		"""Check whether the given name is a valid Lean identifier"""

		return (LeanWriter.allowed_char(name[:1], first=True) and
		        all(LeanWriter.allowed_char(c) for c in name))

	def _translate_name(self, name: str):
		"""Translate operator name"""

		if not self.opts.get('prefer-quotes', False):
			name = ''.join(self.ID_REPLACE_MAP.get(c, c) for c in name)

		# Names starting with _ are reserved for the system in Lean
		elif name.startswith('_'):
			name = name.lstrip('_')

		# Quotes can be used to allow almost any character in a Lean identifier
		if name and not self._allowed_identifier(name):
			name = f'«{name}»'

		# Use the name join by default for yuxtaposition operators
		return name if name else 'join'

	@staticmethod
	def _make_call(name: str, args):
		"""Build a function call for Lean"""
		return f'({name} {" ".join(args)})' if args else name

	def _translate_term(self, term: maude.Term, kind: maude.Kind = None):
		"""Translate a term to Lean"""

		# Variables are made lowercase
		if term.isVariable():
			return term.getVarName().lower()

		# The operator name is its_kind.name or simply name when kind = its_kind
		# (i.e. when we are writing this term in its_kind's namespace)
		symbol = term.symbol()
		range_kind = symbol.getRangeSort().kind()
		name = (f'{self.kinds[range_kind]}.' if range_kind != kind else '') + self.symbols[symbol]

		if symbol.arity() == 0:
			return name

		args = [self._translate_term(subterm, kind=kind) for subterm in term.arguments()]

		# Associative term are flattened in Maude, but not in Lean (except with notation)
		if symbol.isAssoc() and len(args) > 2:
			rhs = f'({name} {args[-2]} {args[-1]})'
			for k in reversed(range(len(args) - 2)):
				rhs = f'({name} {args[k]} {rhs})'
			return rhs

		return self._make_call(name, args)

	def _sort_kinds(self):
		"""Sort kinds topologically (as a preorder)"""

		# Kinds are separated into strongly connected components, i.e.
		# into groups of mutually inductive types

		graph = Graph()

		for op in self.mod.getSymbols():
			kind = op.getRangeSort().kind()
			graph.add_vertex(kind)

			for i in range(op.arity()):
				subkind = op.domainKind(i)
				if kind != subkind:
					graph.add_edge(kind, subkind)

		self.kind_ordering = graph.topological_scc()

	def _index_kinds(self):
		"""Index kind-related stuff"""

		# Kinds are represented as k<first sort name>
		self.kinds = {k: f'k{k.sort(1)}' for k in self.mod.getKinds()}
		self._sort_kinds()

		# Whole kind sorts for error-free kinds (if enabled)
		self.whole_kind_sorts = {k.sort(1) for k in self.mod.getKinds()
		                         if k.errorFree() and k.nrMaximalSorts() == 1} \
			if self.opts.get('with-error-free-opt', False) else set()

	def _index_symbols(self):
		"""Index symbols"""

		# Mapping from symbols to their names
		self.symbols = {}
		# Kind-indexed collection of symbols
		self.symbols_kind = {}

		non_empty_kinds = set()

		# The user-provided renaming of symbols (if any)
		op_renaming = self.opts.get('op-renaming', {})

		for op in self.mod.getSymbols():
			range_sort = op.getRangeSort()
			range_kind = range_sort.kind()

			# Maude introduce some artificial symbols for variables
			# that the library does not hide appropriately
			if str(range_sort) == str(op):
				continue

			# We record which kinds are empty (unusual, except in parameterized modules)
			if range_kind not in non_empty_kinds:
				non_empty_kinds.add(range_kind)

			# Translate the Maude name to a valid Lean identifier
			name = str(op)
			name = op_renaming.get(name) if name in op_renaming else self._translate_name(name)

			self.symbols[op] = name
			self.symbols_kind.setdefault(range_kind, []).append(op)

		# List of empty kinds (in order to avoid non-determinism)
		self.empty_kinds = [k for k in self.kinds if k not in non_empty_kinds]

		# Avoid name clashes within the same kind
		# (overloading is not supported by Lean except with notation)
		for kind, ops in self.symbols_kind.items():
			total_uses = Counter(self.symbols[op] for op in ops)
			current_uses = Counter()

			for op in ops:
				name = self.symbols[op]

				if total_uses[name] > 1:
					self.symbols[op] = name + subindex(current_uses[name])
					current_uses[name] += 1

	def _index_module(self):
		"""Index module members"""

		self._index_kinds()
		self._index_symbols()

		self.all_mbs = self._index_statements('mb', self.mod.getMembershipAxioms())
		self.all_eqs = self._index_statements('eq', self.mod.getEquations())
		self.all_rls = self._index_statements('rl', self.mod.getRules())

		# Index structural axioms by kind
		self.all_axioms = {}

		for op, axioms in self.mlu.structural_axioms(self.mod).items():
			self.all_axioms.setdefault(op.getRangeSort().kind(), []).append((op, axioms))

	def _index_statements(self, prefix: str, stmts):
		"""Index statements by kind"""

		names_by_kind = {}

		# First pass, generate names for the statements
		for stmt in stmts:
			lhs, label = stmt.getLhs(), stmt.getLabel()
			lhs_symbol = lhs.symbol()

			# In absence of a label, the top symbol name is used
			if not label:
				# The default value is for variables
				label = self.symbols.get(lhs_symbol, str(lhs_symbol).lower())

			names = names_by_kind.setdefault(lhs_symbol.getRangeSort().kind(), [])
			names.append((stmt, f'{prefix}_{label}'))

		stmt_by_kind = {}

		# Second phase, avoid name clashes by adding indices
		for kind, names in names_by_kind.items():
			total_uses = Counter(name for _, name in names)
			current_uses = Counter()

			current = []

			for stmt, name in names:
				# Indices are added only when there are homonym statements
				if total_uses[name] > 1:
					index = current_uses[name]
					current_uses[name] += 1
					name += subindex(index)

				current.append((stmt, name))

			stmt_by_kind[kind] = current

		return stmt_by_kind

	def _make_fragment(self, fragment: maude.ConditionFragment):
		"""Build a Lean term for a condition fragment"""
		lhs = fragment.getLhs()
		kind = self.kinds[lhs.getSort().kind()]
		lhs = self._translate_term(lhs)

		if isinstance(fragment, maude.EqualityCondition) or isinstance(fragment, maude.AssignmentCondition):
			return f'{kind}.eqe {lhs} {self._translate_term(fragment.getRhs())}'
		if isinstance(fragment, maude.SortTestCondition):
			return f'{kind}.has_sort {lhs} MSort.{fragment.getSort()}'
		if isinstance(fragment, maude.RewriteCondition):
			return f'{kind}.rw_star {lhs} {self._translate_term(fragment.getRhs())}'

	def _make_condition(self, condition: maude.Condition):
		"""Build a Lean term for a Maude condition"""
		return (self._make_fragment(f) for f in condition)

	def _use_notation(self, name: str):
		"""Whether notation should be used for a given relation"""
		return (name in self.opts.get('use-notation', ()) or
		        name in self.opts.get('declare-notation', ()))

	def _declare_notation(self, lean: LeanWriter, option_key: str, default_sym: str, relation: str):
		"""Declare infix notation for the given relation"""
		if not self._use_notation(relation):
			return 

		symbol = self.opts.get(option_key, default_sym)
		for kind in self.kinds.values():
			lean.decl_notation(symbol, 40, f'{kind}.{relation}')

		lean.newline()

	@staticmethod
	def _is_proper_sort(sort: maude.Sort):
		"""Whether it is a proper sort or an error sort"""
		return not str(sort).startswith('[')

	def _make_premise(self, stmt):
		"""Make a premise for a statement"""

		# Get all the variables in the statement
		varset = get_variables_stmt(stmt)

		# Build sort membership clauses for the variables in a statement
		sort_premise = (f'{self.kinds[var.getSort().kind()]}.has_sort {var.getVarName().lower()} MSort.{var.getSort()}'
		                for var in varset if self._is_proper_sort(var.getSort())
		                and var.getSort() not in self.whole_kind_sorts)

		return chain(sort_premise, self._make_condition(stmt.getCondition()))

	@staticmethod
	def _make_chain(*clauses: str):
		"""Make a chain of implications"""
		return ' → '.join(clauses)

	def _do_sorts(self, lean: LeanWriter):
		"""Handle sorts"""

		lean.newline()
		lean.comment('Sorts')

		# List of sorts excluding error sorts
		sorts = tuple(filter(self._is_proper_sort, self.mod.getSorts()))

		lean.begin_inductive('MSort')

		for s in sorts:
			lean.inductive_ctor(str(s))

		lean.end_inductive()

		lean.newline()
		lean.comment('Generator of the subsort relation')

		lean.begin_def('subsort', 'MSort', 'MSort', 'Prop')

		for s in sorts:
			for sb in s.getSubsorts():
				lean.def_case(f'MSort.{sb} MSort.{s}', 'true')

		lean.def_case('_ _', 'false')
		lean.end_def()

	def _do_ctor_only4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Define a ctor_only predicate for the given kind"""
		kind_name = self.kinds[kind]

		for op in self.symbols_kind[kind]:
			# In principle, the constructor flag is specific to a declaration
			# (i.e. a symbol can be a constructor for some argument sorts and
			# not for others) but we do not make that distinction
			if any(d.isConstructor() for d in op.getOpDeclarations()):
				name, variables = self.symbols[op], make_variables('a', op.arity())
				lhs = self._make_call(f'{kind_name}.{name}', variables)
				rhs = ' ∧ '.join(f'{var}.ctor_only' for var in variables)
				lean.def_case(lhs, rhs if rhs else 'true')

		lean.def_case('_', 'false')

	def _do_mutual_or_simple(self, lean: LeanWriter, kinds, name: str, rtype: str, callback, is_def=False):
		"""Make a mutual or simple declaration"""

		# Give their definitions
		if len(kinds) == 1:
			(kind, kind_name), *_ = kinds.items()
			(lean.begin_def if is_def else lean.begin_inductive)(name.format(kind_name), rtype.format(kind_name))
			callback(lean, kind)
			lean.end_def() if is_def else lean.end_inductive()

		else:
			lean.print('mutual', 'def' if is_def else 'inductive', ', '.join(name.format(kind) for kind in self.kinds.values()))
			for kind, kind_name in kinds.items():
				lean.newline()
				lean.print(f'with {name.format(kind_name)} : {rtype.format(kind_name)}')
				callback(lean, kind)

	def _do_ctor_only(self, lean: LeanWriter):
		"""Define ctor_only predicates"""

		lean.newline()
		lean.comment('Predicates recognizing constructor terms')
		self._do_mutual_or_simple(lean, self.kinds, '{}.ctor_only', '{} → Prop', self._do_ctor_only4kind, is_def=True)

	def _do_symbols4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Handle the symbols with a given target kind"""

		for op in self.symbols_kind[kind]:
			name = self.symbols[op]

			if op.arity() == 0:
				lean.inductive_ctor(name)
			else:
				signature = (self.kinds[op.domainKind(i)] for i in range(op.arity()))
				lean.inductive_ctor(name, *signature, self.kinds[kind])

	def _do_symbols(self, lean: LeanWriter):
		"""Handle kinds and their symbols"""

		lean.newline()
		lean.comment('Kinds and their operators')

		# Empty kinds are defined as constants
		if self.empty_kinds:
			lean.decl_constants('Type', *(self.kinds[v] for v in self.empty_kinds))

		# Explored by SCC in topological ordering
		for scc in self.kind_ordering:
			# Empty kinds are not defined inductively
			if all(v in self.empty_kinds for v in scc):
				continue

			# Prepare a kind to kind name map for _do_mutual_or_simple
			scc_ext = {k: self.kinds[k] for k in scc}

			lean.newline()
			self._do_mutual_or_simple(lean, scc_ext, '{}', 'Type', self._do_symbols4kind)

	def _do_kind_assignment(self, lean: LeanWriter):
		"""Build the function mapping its kind to each sort"""
		lean.newline()
		lean.comment('Kind assignment')

		sorts = tuple(filter(self._is_proper_sort, self.mod.getSorts()))

		lean.begin_def('kind', 'MSort', 'Type')

		for s in sorts:
			lean.def_case(f'MSort.{s}', self.kinds[s.kind()])

		lean.end_def()

	def _make_collapsed_args(self, op: maude.Symbol, names):
		"""Make a list of arguments collapsing those for the same kind"""

		args, kind = f'{{{names[0]}', op.domainKind(0)

		for i, name in enumerate(names[1:], start=1):
			this_kind = op.domainKind(i)
			if this_kind != kind:
				args += f' : {self.kinds[kind]}}} {{{name}'
				kind = this_kind
			else:
				args += f' {name}'

		return f'{args} : {self.kinds[kind]}}}'

	def _make_congruence(self, op: maude.Symbol, relation: str):
		"""Declare a congurence axiom"""

		op_name = self.symbols[op]
		kind_name = self.kinds[op.getRangeSort().kind()]
		full_op_name = f'{kind_name}.{op_name}'
		avars = make_variables('a', op.arity())
		bvars = make_variables('b', op.arity())

		# One variable for each side and argument of the constructor
		args = self._make_collapsed_args(op, [f'{avar} {bvar}' for avar, bvar in zip(avars, bvars)])

		# The premise is a conjunction of relation hypotheses on the arguments
		premise = (f'{self.kinds[op.domainKind(i)]}.{relation} {avar} {bvar}'
		           for i, (avar, bvar) in enumerate(zip(avars, bvars)))
		rhs = ' '.join((f'{kind_name}.{relation}',
		                self._make_call(full_op_name, avars),
		                self._make_call(full_op_name, bvars)))

		return f'{relation}_{op_name} {args} : {self._make_chain(*premise, rhs)}'

	def _do_repr4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Write translation to string for kind"""
		ops = self.symbols_kind[kind]

		# The repr function does not make sense in empty kinds
		# (but we write a dummy definition since others may refer to it)
		if not ops:
			lean.def_case('_', '"<empty>"')
			return

		for op in ops:
			op_name = f'{self.kinds[kind]}.{self.symbols[op]}'
			variables = make_variables('a', op.arity())
			call = self._make_call(op_name, variables)

			if op.arity() == 0:
				lean.def_case(op_name, f'"{op}"')
			else:
				parts = ' ++ ", " ++ '.join(f'({var}.repr)' for var in variables)
				lean.def_case(call, f'"{op}(" ++ {parts} ++ ")"')

	def _do_repr(self, lean: LeanWriter):
		"""Write conversions to string"""

		lean.newline()
		lean.comment('String conversion')

		# Prefix notation is used (infix notation would be better...)
		for scc in self.kind_ordering:
			# Prepare a kind to kind name dictionary for _do_mutual_or_simple
			scc_ext = {k: self.kinds[k] for k in scc}

			lean.newline()
			self._do_mutual_or_simple(lean, scc_ext, '{}.repr', '{} → string', self._do_repr4kind, is_def=True)

		lean.newline()

		# The class has_repr allows showing elements of these types with #eval
		for kind in self.symbols_kind.keys():
			lean.print(f'instance : has_repr {self.kinds[kind]} := ⟨ {self.kinds[kind]}.repr ⟩')

	def _warn_special_ops(self):
		"""Warn about the use of special operators"""

		# Warn about special operators
		bool_hooks = frozenset(('SystemTrue', 'SystemFalse', 'BranchSymbol', 'EqualitySymbol'))

		specials = [op for op, special in self.mlu.special_ops(self.mod) if special not in bool_hooks]

		if specials:
			print(f'\x1b[33;1mWarning:\x1b[0m the Maude module contains {len(specials)} '
			      f'special operators like {specials[0]} whose behavior is not defined '
			      'equationally in Maude.', file=sys.stderr)

	def _do_eqa4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare equality modulo structural axioms for a given kind"""

		kind_name = self.kinds[kind]

		# Equivalence relation constructors
		lean.inductive_ctor('refl {a}', f'{kind_name}.eqa a a')
		lean.inductive_ctor('symm {a b}', f'{kind_name}.eqa a b → {kind_name}.eqa b a')
		lean.inductive_ctor('trans {a b c}', f'{kind_name}.eqa a b → {kind_name}.eqa b c → {kind_name}.eqa a c')

		# Congruence axioms
		lean.comment('\tCongruence axioms for each operator')
		for op in filter(maude.Symbol.arity, self.symbols_kind[kind]):
			lean.print('\t|', self._make_congruence(op, 'eqa'))

		# Structural axioms
		if kind not in self.all_axioms:
			return

		lean.comment('\tStructural axioms')
		for op, axioms in self.all_axioms[kind]:
			op_name = self.symbols[op]
			op_call = f'{kind_name}.{op_name}'

			for axiom, *args in axioms:
				if axiom == 'a':
					lean.inductive_ctor(f'{op_name}_assoc {{a b c}}',
					                    f'{kind_name}.eqa ({op_call} a ({op_call} b c)) '
					                    f'({op_call} ({op_call} a b) c)')
				elif axiom == 'c':
					lean.inductive_ctor(f'{op_name}_comm {{a b}}',
					                    f'{kind_name}.eqa ({op_call} a b) ({op_call} b a)')

				elif axiom in 'lri':
					if axiom != 'r':
						lean.inductive_ctor(f'{op_name}_left_id {{a}}',
						                    f'{kind_name}.eqa ({op_call} {self._translate_term(args[0])} a) a')
					if axiom != 'l':
						lean.inductive_ctor(f'{op_name}_right_id {{a}}',
						                    f'{kind_name}.eqa ({op_call} a {self._translate_term(args[0])}) a')
				elif axiom == 'd':
					lean.inductive_ctor(f'{op_name}_idem {{a}}',
					                    f'{kind_name}.eqa ({op_call} ({op_call} a)) ({op_call} a)')

	def _do_eqa(self, lean: LeanWriter):
		"""Declare an inductive relation for equality modulo structural axioms"""

		lean.newline()
		lean.comment('Equality modulo axioms')

		self._do_mutual_or_simple(lean, self.kinds, '{}.eqa', '{0} → {0} → Prop', self._do_eqa4kind)

	def _do_implicit_memberships(self, lean: LeanWriter, ops: list[maude.Symbol]):
		"""Do the implicit memberships"""

		labels = []

		for op in ops:
			name = self.symbols[op]
			kind_name = self.kinds[op.getRangeSort().kind()]
			variables = make_variables('a', op.arity())
			decls = list(op.getOpDeclarations())

			for k, decl in enumerate(decls):
				*domain, range_sort = decl.getDomainAndRange()

				# Declarations at the kind level do not imply a membership axiom
				if not self._is_proper_sort(range_sort):
					continue

				args = self._make_collapsed_args(op, variables) + ' ' if op.arity() else ''
				condition = (f'{self.kinds[mtype.kind()]}.has_sort {var} MSort.{mtype}'
				             for var, mtype in zip(variables, domain)
				             if self._is_proper_sort(mtype))

				label = f'{name}_decl{subindex(k) if len(decls) > 1 else ""}'
				call = self._make_call(f'{kind_name}.{name}', variables)
				body = self._make_chain(*condition, f'{kind_name}.has_sort {call} MSort.{range_sort}')

				lean.print(f'\t| {label} {args}: {body}')
				labels.append(label)

		return labels

	def _do_has_sort4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare the sort membership relation for given kind"""

		kind_name = self.kinds[kind]

		lean.print(f'with {kind_name}.has_sort : {kind_name} → MSort → Prop')
		lean.inductive_ctor('subsort {t a b}',
		                    f'subsort a b → {kind_name}.has_sort t a → {kind_name}.has_sort t b')

		# Implicit membership axioms
		lean.comment('\tImplicit membership axioms (operator declarations)')
		self.impl_mb_axioms[kind] = self._do_implicit_memberships(lean, self.symbols_kind.get(kind, ()))

		# Explicit membership axioms
		if kind not in self.all_mbs:
			return

		lean.comment('\tExplicit membership axioms')
		for mb, label in self.all_mbs[kind]:
			premise = self._make_premise(mb)
			lhs = self._translate_term(mb.getLhs())

			# Variables are added as constructor arguments
			variables = ' '.join(sorted(v.getVarName().lower() for v in get_variables_stmt(mb)))
			variables = f' {{{variables}}}' if variables else ''

			lean.inductive_ctor(f'{label}{variables}', *premise,
			                    f'{kind_name}.has_sort {lhs} MSort.{mb.getSort()}')

	def _do_eqe4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare equality modulo equations for a given kind"""

		kind_name = self.kinds[kind]

		lean.print(f'with {kind_name}.eqe : {kind_name} → {kind_name} → Prop')
		lean.inductive_ctor('from_eqa {a b}', f'{kind_name}.eqa a b → {kind_name}.eqe a b')
		lean.inductive_ctor('symm {a b}', f'{kind_name}.eqe a b → {kind_name}.eqe b a')
		lean.inductive_ctor('trans {a b c}', f'{kind_name}.eqe a b → {kind_name}.eqe b c → {kind_name}.eqe a c')

		# Congruence axioms
		lean.comment('\tCongruence axioms for each operator')
		for op in filter(maude.Symbol.arity, self.symbols_kind[kind]):
			lean.print('\t|', self._make_congruence(op, 'eqe'))

		# Equations
		if kind not in self.all_eqs:
			return

		lean.comment('\tEquations')
		for eq, label in self.all_eqs[kind]:
			premise = self._make_premise(eq)
			lhs = self._translate_term(eq.getLhs())
			rhs = self._translate_term(eq.getRhs())

			# Variables are added as constructor arguments
			variables = ' '.join(sorted(v.getVarName().lower() for v in get_variables_stmt(eq)))
			variables = f' {{{variables}}}' if variables else ''

			lean.inductive_ctor(f'{label}{variables}', *premise, f'{kind_name}.eqe {lhs} {rhs}')

	def _do_equational_relations(self, lean: LeanWriter):
		"""Declare the equational relations"""

		lean.newline()
		lean.comment('Sort membership and equality modulo equations')
		lean.newline()

		lean.print('mutual inductive', ', '.join(f'{kind}.{rel}' for rel in ('has_sort', 'eqe')
		                                         for kind in self.kinds.values()))

		# Sort membership relation
		for kind in self.kinds:
			self._do_has_sort4kind(lean, kind)
			lean.newline()

		# Equational relation
		for kind in self.kinds:
			self._do_eqe4kind(lean, kind)
			lean.newline()

		# Introduce notation (if desired)
		self._declare_notation(lean, 'has-sort-symbol', '⊳', 'has_sort')
		self._declare_notation(lean, 'eqa-symbol', '=A', 'eqa')
		self._declare_notation(lean, 'eqe-symbol', '=E', 'eqe')

	def _do_rw_one4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare the one-step sequential rule rewrite relation for the given kind"""

		kind_name = self.kinds[kind]

		lean.print(f'with {kind_name}.rw_one : {kind_name} → {kind_name} → Prop')
		lean.inductive_ctor('eqe_left {a b c}',
		                    f'{kind_name}.eqe a b → {kind_name}.rw_one b c → {kind_name}.rw_one a c')
		lean.inductive_ctor('eqe_right {a b c}',
		                    f'{kind_name}.rw_one a b → {kind_name}.eqe b c → {kind_name}.rw_one a c')

		# A rewrite in a subterm is a rewrite in the whole term
		lean.comment('\tAxioms for rewriting inside subterms')
		for op in self.symbols_kind.get(kind, ()):
			op_name = self.symbols[op]
			variables = make_variables('a', op.arity())
			for i in range(op.arity()):
				args = ' '.join(variables[:i] + variables[i+1:] + ('a', 'b'))
				label = f'sub_{op_name}{subindex(i) if op.arity() > 1 else ""}'
				lean.inductive_ctor(f'{label} {{{args}}}', f'{self.kinds[op.domainKind(i)]}.rw_one a b →'
				                    f'\n\t\t{kind_name}.rw_one ' +
				                    self._make_call(f'{kind_name}.{op_name}', replace(variables, i, 'a')) + ' ' +
				                    self._make_call(f'{kind_name}.{op_name}', replace(variables, i, 'b')))

		# Rewrite rules
		if kind not in self.all_rls:
			return

		lean.comment('\tRewrite rules')
		for rl, label in self.all_rls.get(kind, ()):
			premise = self._make_premise(rl)
			lhs = self._translate_term(rl.getLhs())
			rhs = self._translate_term(rl.getRhs())

			# Variables are added as constructor arguments
			variables = ' '.join(sorted(v.getVarName().lower() for v in get_variables_stmt(rl)))
			variables = f' {{{variables}}}' if variables else ''

			lean.inductive_ctor(f'{label}{variables}', *premise, f'{kind_name}.rw_one {lhs} {rhs}')

	def _do_rewriting_relations(self, lean: LeanWriter):
		"""Declare the rewriting relations"""

		lean.comment('Rewriting relations')
		lean.newline()

		lean.print('mutual inductive', ', '.join(f'{kind}.{rel}' for rel in ('rw_one', 'rw_star')
		                                         for kind in self.kinds.values()))

		# One-step relation
		for kind in self.kinds:
			self._do_rw_one4kind(lean, kind)
			lean.newline()

		# Transitive and reflective closure
		# (we could define as the reflexive and transitive closure by a definition,
		# but the one step relation may have mutual dependencies with this one)
		for kind, kind_name in self.kinds.items():
			lean.print(f'with {kind_name}.rw_star : {kind_name} → {kind_name} → Prop')
			lean.inductive_ctor('step {a b}', f'{kind_name}.rw_one a b → {kind_name}.rw_star a b')
			lean.inductive_ctor('refl {a b}', f'{kind_name}.eqe a b → {kind_name}.rw_star a b')
			lean.inductive_ctor('trans {a b c}', f'{kind_name}.rw_star a b → {kind_name}.rw_star b c → {kind_name}.rw_star a c')
			lean.newline()

		# Introduce notation (if desired)
		self._declare_notation(lean, 'rw-one-symbol', '=>1', 'rw_one')
		self._declare_notation(lean, 'rw-star-symbol', '=>*', 'rw_star')

	def _do_equational_attrs4kind(self, lean: LeanWriter, kind: maude.Kind,
	                              simp_extra: list[str], congr_extra: list[str]):
		"""Declare Lean attributes for the different standard axioms"""

		lean.comment('Attributes for the Lean simplifier and machinery')

		lean.print('attribute [refl] eqa.refl')
		lean.print('attribute [symm] eqa.symm eqe.symm')
		lean.print('attribute [trans] eqa.trans eqe.trans')

		# Congruence axioms
		congr_labels = []

		for op in filter(maude.Symbol.arity, self.symbols_kind.get(kind, ())):
			congr_labels.append(f'eqa.eqa_{self.symbols[op]}')
			congr_labels.append(f'eqe.eqe_{self.symbols[op]}')

		if congr_labels or congr_extra:
			lean.print('attribute [congr]', ' '.join(congr_labels + congr_extra))

		# Definitions for the simplifier
		simp_labels = ([f'has_sort.{label}' for label in self.impl_mb_axioms[kind]] +
		               [f'has_sort.{label}' for mb, label in self.all_mbs.get(kind, ()) if not mb.isNonexec()] +
		               [f'eqe.{label}' for eq, label in self.all_eqs.get(kind, ()) if not eq.isNonexec()] +
		               simp_extra)

		if simp_labels:
			lean.print('attribute [simp]', ' '.join(simp_labels))

	def _do_rewriting_attrs4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare Lean attributes for the standard axiom of the rewriting relations"""

		lean.newline()
		lean.comment('Attributes for the Lean simplifier and machinery')

		lean.print('attribute [refl] rw_star.refl')
		lean.print('attribute [trans] rw_star.trans')

	def _do_equational_aliases4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare aliases for equational definitions for the given kind"""

		lean.comment('Aliases')

		# Structural axioms
		axiom_names = {
			'a': 'assoc',
			'c': 'comm',
			'l': 'left_id',
			'r': 'right_id',
			'i': 'id',
			'd': 'idem'
		}

		for op, axioms in self.all_axioms.get(kind, ()):
			op_name = self.symbols[op]

			for axiom, *_ in axioms:
				if axiom != 'i':
					label = f'{op_name}_{axiom_names[axiom]}'
					lean.print(f'def {label} := @eqa.{label}')

		# Implicit membership axioms
		for label in self.impl_mb_axioms.get(kind, ()):
			lean.print(f'def {label} := @has_sort.{label}')

		# Explicit membership axioms
		for _, label in self.all_mbs.get(kind, ()):
			lean.print(f'def {label} := @has_sort.{label}')

		# Congruence axioms
		for op in filter(maude.Symbol.arity, self.symbols_kind[kind]):
			op_name = self.symbols[op]
			lean.print(f'def eqa_{op_name} := @eqa.eqa_{op_name}')
			lean.print(f'def eqe_{op_name} := @eqe.eqe_{op_name}')

		# Equations
		for _, label in self.all_eqs.get(kind, ()):
			lean.print(f'def {label} := @eqe.{label}')

	def _do_lemmas(self, lean: LeanWriter):
		"""Introduce lemmas for the axioms"""

		lean.comment('Lemmas and aliases')

		# Write a generic congruence lemma for proving congruences
		lean.newline()
		lean.print(pkg_resources.read_text(data, 'generic_congr.lean'))

		for kind, kind_name in self.kinds.items():

			# They are put in their kind's namespace
			lean.begin_namespace(kind_name)

			# Axioms that will be added the simp attribute
			simp_axioms = []

			lean.comment('Sort membership lemmas')

			# Subsort relations
			for sort in map(kind.sort, range(1, kind.nrSorts())):
				for subsort in sort.getSubsorts():
					label = f'subsort_{str(subsort).lower()}_{str(sort).lower()}'
					lean.print(f'lemma {label} {{t : {kind_name}}} :',
					           f't{self.has_sort}MSort.{subsort} →\n\t'
					           f't{self.has_sort}MSort.{sort}',
					           ':= by apply has_sort.subsort; simp [subsort]')

					simp_axioms.append(label)

			lean.newline()
			lean.comment('Reflexivity and congruence lemmas')

			lean.print(f'@[refl] lemma eqe_refl (a : {kind_name}) : a{self.eqe}a := eqe.from_eqa eqa.refl')

			# Congruence axiom for the relations themselves
			lean.print(f'lemma eqa_congr {{a b c d : {kind_name}}} : a{self.eqa}b → c{self.eqa}d → '
			           f'(a{self.eqa}c) = (b{self.eqa}d)\n\t:= generic_congr @eqa.trans @eqa.trans @eqa.symm')
			lean.print(f'lemma eqe_congr {{a b c d : {kind_name}}} : a{self.eqe}b → c{self.eqe}d → '
			           f'(a{self.eqe}c) = (b{self.eqe}d)\n\t:= generic_congr @eqe.trans @eqe.trans @eqe.symm')
			lean.print(f'lemma eqa_eqe_congr {{a b c d : {kind_name}}} : a{self.eqa}b → c{self.eqa}d → '
			           f'(a{self.eqe}c) = (b{self.eqe}d)\n\t:= generic_congr '
			           '(λ x y z, (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))\n\t\t'
			           '(λ x y z h, (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm')

			congr_axioms = ['eqa_congr', 'eqe_congr', 'eqa_eqe_congr']

			# Write shorter aliases for some definitions
			if self.opts.get('with-aliases', True):
				lean.newline()
				self._do_equational_aliases4kind(lean, kind)

			# Activate the membership axioms for the Lean simplifier
			if self.opts.get('with-simp', True):
				lean.newline()
				self._do_equational_attrs4kind(lean, kind, simp_axioms, congr_axioms)

			lean.end_namespace()

		if not self.opts.get('with-rules', True):
			return

		lean.newline()
		lean.comment('Lemmas for the rewriting relation')

		# Write the generic infer_sub_star tactic
		lean.print('\n' + pkg_resources.read_text(data, 'infer_sub_star.lean'))

		for kind, kind_name in self.kinds.items():
			lean.begin_namespace(kind_name)

			# Congruence lemmas with respect to =E and =A
			lean.comment('Congruence lemmas')

			lean.print(f'@[congr] lemma eqe_rw_one_congr {{a b c d : {kind_name}}} : a{self.eqe}b → c{self.eqe}d → '
			           f'(a{self.rw_one}c) = (b{self.rw_one}d)\n\t:= generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm')
			lean.print(f'@[congr] lemma eqa_rw_one_congr {{a b c d : {kind_name}}} : a{self.eqa}b → c{self.eqa}d → '
			           f'(a{self.rw_one}c) = (b{self.rw_one}d)\n\t:= generic_congr '
			           '(λ x y z, (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))\n\t\t'
			           '(λ x y z h, (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm')
			lean.print(f'@[congr] lemma eqe_rw_star_congr {{a b c d : {kind_name}}} : a{self.eqe}b → c{self.eqe}d → '
			           f'(a{self.rw_star}c) = (b{self.rw_star}d)\n\t:= generic_congr '
			           '(λ x y z, (@rw_star.trans x y z) ∘ (@rw_star.refl x y))\n\t\t'
			           '(λ x y z h, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm')
			lean.print(f'@[congr] lemma eqa_rw_star_congr {{a b c d : {kind_name}}} : a{self.eqa}b → c{self.eqa}d → '
			           f'(a{self.rw_star}c) = (b{self.rw_star}d)\n\t:= generic_congr '
			           '(λ x y z, (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))\n\t\t'
			           '(λ x y z h, (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm')

			# Aliases for the rewrite rules
			if self.opts.get('with-aliases', True) and kind in self.all_rls:
				lean.newline()
				lean.comment('Aliases for rewrite rules')
				for rl, label in self.all_rls.get(kind, ()):
					lean.print(f'def {label} := @rw_one.{label}')

			# Attributes (even without with-simp, since they are required for the lemmas)
			self._do_rewriting_attrs4kind(lean, kind)

			# Subterm rewriting lemmas for =>*
			lean.newline()
			lean.comment('Lemmas for subterm rewriting with =>*')

			for op in self.symbols_kind.get(kind, ()):
				op_name = self.symbols[op]
				variables = make_variables('a', op.arity())
				for i in range(op.arity()):
					args = [f'{var}' if j != i else 'a b' for j, var in enumerate(variables)]
					args = self._make_collapsed_args(op, args)
					label = f'sub_{op_name}{subindex(i) if op.arity() > 1 else ""}'
					lean.print(f'lemma rw_star_{label} {args} : a{self.rw_star}b →\n\t\t'
					           f'{self._make_call(op_name, replace(variables, i, "a"))}{self.rw_star}'
					           f'{self._make_call(op_name, replace(variables, i, "b"))} := by '
					           f'infer_sub_star ``(rw_one.{label}) ``(eqe.eqe_{op_name})')

			lean.end_namespace()

	def translate(self, lean: LeanWriter):
		"""Do the translation"""

		# By default, everything is inserted into the Maude namespace
		outermost_namespace = self.opts.get('outermost-namespace', 'Maude')

		if outermost_namespace:
			lean.print('namespace', outermost_namespace)

		if len(self.mod.getSorts()) == 0:
			lean.print('\t-- Empty module\nend Maude')
			return

		self._warn_special_ops()

		# This is the same as in the axiomatic translation
		self._do_sorts(lean)
		self._do_symbols(lean)
		if self.opts.get('with-sort2kind', True):
			self._do_kind_assignment(lean)
		if self.opts.get('with-ctor-predicate', True):
			self._do_ctor_only(lean)

		self._do_eqa(lean)
		self._do_equational_relations(lean)

		if self.opts.get('with-rules', True):
			self._do_rewriting_relations(lean)

		if self.opts.get('with-lemmas', True):
			self._do_lemmas(lean)

		if self.opts.get('with-repr', True):
			self._do_repr(lean)

		if outermost_namespace:
			lean.print('\nend', outermost_namespace)
