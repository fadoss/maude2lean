#
# Transform a Maude module into a Lean specification
#

import importlib.resources as pkg_resources
from collections import Counter
from itertools import chain

import maude

from . import data, maudext, special
from . import diagnostics as diag
from .def_extractor import get_simple_derived_symbols
from .graph import Graph
from .lean import LeanWriter
from .maudext import is_ctor


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


def unique(iterable):
	"""Remove duplicates from an iterable"""
	seen = set()
	for item in iterable:
		if item not in seen:
			seen.add(item)
			yield item


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

	# Structural axioms names
	AXIOM_NAMES = {
		'a': 'assoc',
		'c': 'comm',
		'l': 'left_id',
		'r': 'right_id',
		'i': 'id',
		'd': 'idem'
	}

	def __init__(self, module: maude.Module, opts: dict, verbose=False):
		self.mod = module  # Module we are translating
		self.opts = opts  # User options
		self.verbose = verbose  # Verbosity level

		# Relation names
		self.has_sort = '.has_sort '
		self.eqa = '.eqa '
		self.eqe = '.eqe '
		self.rw_one = '.rw_one '
		self.rw_star = '.rw_star '

		use_notation = opts['use-notation']

		if 'eqa' in use_notation:
			self.eqa = ' ' + opts['eqa-symbol'] + ' '

		if 'eqe' in use_notation:
			self.eqe = ' ' + opts['eqe-symbol'] + ' '

		if 'has_sort' in use_notation:
			self.has_sort = ' ' + opts['has-sort-symbol'] + ' '

		if 'rw_one' in use_notation:
			self.rw_one = ' ' + opts['rw-one-symbol'] + ' '

		if 'rw_star' in use_notation:
			self.rw_star = ' ' + opts['rw-star-symbol'] + ' '

		# Implicit membership axiom labels (per kind)
		self.impl_mb_axioms = {}

		# Lean version
		self.lean_version = opts['lean-version']

		self._index_module()

	@staticmethod
	def _allowed_identifier(name: str):
		"""Check whether the given name is a valid Lean identifier"""

		return (LeanWriter.allowed_char(name[:1], first=True) and
		        all(LeanWriter.allowed_char(c) for c in name))

	def _translate_name(self, name: str):
		"""Translate Maude name"""

		if not self.opts['prefer-quotes']:
			name = ''.join(self.ID_REPLACE_MAP.get(c, c) for c in name)

		# Names starting with _ are reserved for the system in Lean
		# (the replacement map does this fix when not prefer-quotes)
		elif name.startswith('_'):
			name = name.lstrip('_')

		# Quotes can be used to allow almost any character in a Lean identifier
		if name and not self._allowed_identifier(name):
			name = f'«{name}»'

		# Use the name join by default for juxtaposition operators
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

		# Order the kinds in each connected components by
		# alphabetical order to avoid non-determinism
		self.kind_ordering = [sorted(scc, key=lambda k: self.kinds[k])
		                      for scc in self.kind_ordering]

	@staticmethod
	def _is_proper_sort(sort: maude.Sort):
		"""Whether it is a proper sort or an error sort"""
		return not str(sort).startswith('[')

	def _index_sorts(self):
		"""Index sorts"""

		# List of sorts excluding error sorts
		sorts = tuple(filter(self._is_proper_sort, self.mod.getSorts()))

		# The user-provided renaming of sorts (if any)
		sort_renaming = self.opts['sort-renaming']

		# Name sorts according to the renaming and the Lean constraints
		self.sorts = {sort: self._translate_name(sort_renaming.get(str(sort), str(sort)))
		              for sort in sorts}

	def _apply_error_free_opt(self):
		"""Apply the error-free kind optimization"""

		for k in self.mod.getKinds():
			candidate = k.sort(1)

			# The kind must be error and and have a single main sort
			if k.errorFree() and k.nrMaximalSorts() == 1:
				self.whole_kind_sorts.add(candidate)
				if self.verbose:
					diag.info(f'{candidate} is a whole-kind sort.')

			# Show why the optimization does not succeed
			elif self.verbose:
				causes = []
				if not k.errorFree():
					causes.append('is not error-free')
				if k.nrMaximalSorts() != 1:
					causes.append('contains multiple maximal sorts')
				diag.info(f'{k} {" and ".join(causes)}.')

	def _index_kinds(self):
		"""Index kind-related stuff"""

		# The user-provided renaming of kinds
		kind_renaming = {}

		for sort_name, kind_name in self.opts['kind-renaming'].items():
			# Any sort in the kind can be used as key
			# (no warning if the sort is not valid)
			if sort := self.mod.findSort(sort_name):
				kind_renaming[sort.kind()] = kind_name

		# Kinds are represented as k<first sort name> by default
		self.kinds = {k: kind_renaming.get(k, f'k{self.sorts[k.sort(1)]}')
		              for k in self.mod.getKinds()}
		self._sort_kinds()

		# Whole kind sorts for error-free kinds (if enabled)
		self.whole_kind_sorts = set()

		if self.opts['with-error-free-opt']:
			self._apply_error_free_opt()

	def _index_symbols(self):
		"""Index symbols"""

		# Mapping from symbols to their names
		self.symbols = {}
		# Kind-indexed collection of symbols
		self.symbols_kind = {}

		non_empty_kinds = set()

		# The user-provided renaming of symbols (if any)
		op_renaming = self.opts['op-renaming']

		for op in self.mod.getSymbols():
			range_sort = op.getRangeSort()
			range_kind = range_sort.kind()

			# Maude introduce some artificial symbols for variables
			# that the library does not hide appropriately
			if op.getLineNumber() == '<automatic>':
				continue

			# We record which kinds are empty (unusual, except in parameterized modules)
			if range_kind not in non_empty_kinds:
				non_empty_kinds.add(range_kind)

			# Translate the Maude name to a valid Lean identifier
			name = str(op)
			name = op_renaming[name] if name in op_renaming else self._translate_name(name)

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

		self._index_sorts()
		self._index_kinds()
		self._index_symbols()

		# Index special symbols
		extra_eqs = self._index_specials()

		self.all_mbs = self._index_statements('mb', self.mod.getMembershipAxioms())
		self.all_eqs = self._index_statements('eq', chain(self.mod.getEquations(), extra_eqs))
		self.all_rls = self._index_statements('rl', self.mod.getRules())

		# Index structural axioms by kind
		self.all_axioms = {}

		for op, axioms in maudext.get_structural_axioms(self.mod).items():
			self.all_axioms.setdefault(op.getRangeSort().kind(), []).append((op, axioms))

		# If explicitly selected, non-constructor symbols are translated to
		# constants outside the inductive type (this only make sense when the
		# module is sufficiently complete and constructor terms can be taken
		# without loss of generality). The with-derived-as-defs option below
		# is independent and complements this one.
		self.only_ctors = self.opts['with-derived-as-consts']

		# If explicitly selected in the configuration, check whether some
		# symbols can be translated to Lean definitions instead of cases
		# of the inductive type (or constants) for the corresponding kind.
		self.derived_defs = []

		if self.opts['with-derived-as-defs']:
			self._extract_defs()

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
			else:
				# Labels of parameter modules are prefixed with the invalid $
				label = label.replace('$', '_')

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

	def _index_specials(self):
		"""Index special operators"""

		return special.special_equations(self.mod)

	def _extract_defs(self):
		"""Extract Lean definitions from derived Maude operators"""

		# Get the compatible symbols
		self.derived_defs, recursive = get_simple_derived_symbols(self.mod, verbose=self.verbose)

		# Warn about not checking termination
		if recursive or any(len(ops) > 1 for ops, _ in self.derived_defs):
			diag.warning('recursive definitions are not checked to be terminating.'
			             ' Lean will complain if they are not.')

		# Remove those symbols and equations from the index
		for scc, _ in self.derived_defs:
			for symb, eqs in scc:
				kind = symb.getRangeSort().kind()

				self.symbols_kind[kind].remove(symb)
				self.all_eqs[kind] = [eql for eql in self.all_eqs[kind]
				                      if eql[0] not in eqs]  # eql = (eq, label)

	def _make_fragment(self, fragment: maude.ConditionFragment):
		"""Build a Lean term for a condition fragment"""
		lhs = fragment.getLhs()
		kind = self.kinds[lhs.getSort().kind()]
		lhs = self._translate_term(lhs)

		if isinstance(fragment, maude.EqualityCondition) or isinstance(fragment, maude.AssignmentCondition):
			return f'{kind}.eqe {lhs} {self._translate_term(fragment.getRhs())}'
		if isinstance(fragment, maude.SortTestCondition):
			return f'{kind}.has_sort {lhs} MSort.{self.sorts[fragment.getSort()]}'
		if isinstance(fragment, maude.RewriteCondition):
			return f'{kind}.rw_star {lhs} {self._translate_term(fragment.getRhs())}'

	def _make_condition(self, condition: maude.Condition):
		"""Build an iterator over the translated fragments of a Maude condition"""
		return (self._make_fragment(f) for f in condition)

	def _use_notation(self, name: str):
		"""Whether notation should be used for a given relation"""
		return (name in self.opts['use-notation'] or
		        name in self.opts['declare-notation'])

	def _declare_notation(self, lean: LeanWriter, option_key: str, relation: str):
		"""Declare infix notation for the given relation"""
		if not self._use_notation(relation):
			return

		symbol = self.opts[option_key]
		for kind in self.kinds.values():
			lean.decl_notation(symbol, 40, f'{kind}.{relation}')

		lean.newline()

	def _make_premise(self, stmt):
		"""Make a premise for a statement"""

		# Get all the variables in the statement
		varset = maudext.get_variables_stmt(stmt)

		# Build sort membership clauses for the variables in a statement
		sort_premise = (f'{self.kinds[var.getSort().kind()]}.has_sort '
		                f'{var.getVarName().lower()} MSort.{self.sorts[var.getSort()]}'
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

		lean.begin_inductive('MSort')

		for sort_name in self.sorts.values():
			lean.inductive_ctor(sort_name)

		lean.end_inductive()

		lean.newline()
		lean.comment('Generator of the subsort relation')

		lean.begin_def('subsort', 'MSort', 'MSort', 'Prop')

		for s, sort_name in self.sorts.items():
			# Subsorts may be repeated due to a bug in Maude, so we use unique
			for sb in unique(s.getSubsorts()):
				lean.def_case('true', f'MSort.{self.sorts[sb]}', f'MSort.{sort_name}')

		lean.def_case('false', '_', '_')
		lean.end_def()

	def _do_ctor_only4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Define a ctor_only predicate for the given kind"""
		kind_name = self.kinds[kind]

		symbols = self.symbols_kind.get(kind, ())

		# For empty sorts, we set that everything is a constructor
		# term since there are no defined operators on them
		if not symbols:
			lean.def_case('true', '_')
			return

		pending_symbols = len(symbols)

		for op in filter(is_ctor, symbols):
			name, variables = self.symbols[op], make_variables('a', op.arity())
			lhs = self._make_call(f'{kind_name}.{name}', variables)
			rhs = ' ∧ '.join(f'{var}.ctor_only' for var in variables)
			lean.def_case(rhs if rhs else 'true', lhs)
			pending_symbols -= 1

		# Terms with any other operator (if there is one) are not ctor_only
		if pending_symbols and not self.only_ctors:
			lean.def_case('false', '_')

	def _do_mutual_or_simple(self, lean: LeanWriter, kinds, name: str, rtype: str, callback, is_def=False):
		"""Make a mutual or simple declaration"""

		# This function writes a single or mutually recursive definition of an
		# inductive relation or function for multiple kinds. The argument name
		# and r(eturn)type are pattern strings depending on the kind name, and
		# callback is called to produce the cases for each kind's definition.

		# Write their definitions
		if len(kinds) == 1:
			begin, end = (lean.begin_def, lean.end_def) if is_def else \
			             (lean.begin_inductive, lean.end_inductive)

			(kind, kind_name), = kinds.items()

			begin(name.format(kind_name), rtype.format(kind_name))
			callback(lean, kind)
			end()

		else:
			begin, case = (lean.begin_mutual_def, lean.begin_def) if is_def else \
			              (lean.begin_mutual_inductive, lean.begin_inductive)

			begin(name.format(kind) for kind in kinds.values())

			for kind, kind_name in kinds.items():
				lean.newline()
				case(name.format(kind_name), rtype.format(kind_name))
				callback(lean, kind)

			lean.end_mutual()

	def _do_ctor_only(self, lean: LeanWriter):
		"""Define ctor_only predicates"""

		lean.newline()
		lean.comment('Predicates recognizing constructor terms')
		self._do_mutual_or_simple(lean, self.kinds, '{}.ctor_only', '{} → Prop',
		                          self._do_ctor_only4kind, is_def=True)

	def _make_signature_stream(self, op: maude.Symbol):
		"""Build a type for the given operator signature"""
		signature = tuple(op.domainKind(i) for i in range(op.arity())) + (op.getRangeSort().kind(), )
		return (self.kinds[kind] for kind in signature)

	def _make_signature(self, op: maude.Symbol):
		"""Build a type for the given operator signature"""
		return ' → '.join(self._make_signature_stream(op))

	def _do_derived_defs(self, lean: LeanWriter):
		"""Define derived operators as Lean definitions"""

		if self.derived_defs:
			lean.newline()
			lean.comment('Definition of derived operators outside the inductive type')

		# Mutually-recursive operators are grouped
		for scc, non_comp in self.derived_defs:
			# Qualified names of the operators
			names = {op: f'{self.kinds[op.getRangeSort().kind()]}.{self.symbols[op]}'
			         for op, _ in scc}

			# When using the only_ctors option, definitions depending on
			# constants must be marked noncomputable
			is_comp = not (non_comp and self.only_ctors)

			# Introduce a mutual definition if required
			if len(scc) > 1:
				lean.newline()
				lean.begin_mutual_def(name.values(), computable=is_comp)

			# Write the definition for each operator
			for op, eqs in scc:
				lean.newline()
				signature = self._make_signature_stream(op)

				lean.begin_def(names[op], *signature, computable=is_comp)
				for eq in eqs:
					args = map(self._translate_term, eq.getLhs().arguments())
					lean.def_case(self._translate_term(eq.getRhs()), *args)

			if len(scc) > 1:
				lean.end_mutual()

	def _do_symbols4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Handle the symbols with a given target kind"""

		for op in self.symbols_kind[kind]:
			name = self.symbols[op]

			# Skip symbols that are not constructors
			if self.only_ctors and not is_ctor(op):
				continue

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

			# Prepare a kind to kind-name map for _do_mutual_or_simple
			scc_ext = {k: self.kinds[k] for k in scc}

			lean.newline()
			self._do_mutual_or_simple(lean, scc_ext, '{}', 'Type', self._do_symbols4kind)

		# If the only_ctors option is enabled, non-constructor symbols are
		# defined as constants outside the inductive types for their kinds
		if self.only_ctors:
			self._do_symbols_as_consts(lean)

	def _do_symbols_as_consts(self, lean: LeanWriter):
		"""Declare constants for non-constructor symbols under with-derived-as-consts"""

		lean.newline()
		lean.comment('Non-constructor operators as constants\n'
		             '(enabled by option with-derived-as-consts)')

		for kind, ops in self.symbols_kind.items():
			# Avoid writing empty namespaces when there are no derived symbols
			if ops := tuple(op for op in ops if is_ctor(op)):
				lean.begin_namespace(self.kinds[kind])
				for op in ops:
					lean.decl_constants(self._make_signature(op), self.symbols[op])
				lean.end_namespace()

	def _do_kind_assignment(self, lean: LeanWriter):
		"""Build the function mapping its kind to each sort"""
		lean.newline()
		lean.comment('Kind assignment')

		lean.begin_def('kind', 'MSort', 'Type')

		for s, s_name in self.sorts.items():
			lean.def_case(self.kinds[s.kind()], f'MSort.{s_name}')

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
		"""Declare a congruence axiom"""

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

	def _rewritable_args(self, op: maude.Symbol):
		"""Get the indices of the non-frozen arguments of the symbol"""

		return (set(range(op.arity())) - set(op.getFrozen())
		        if self.opts['with-frozen']
		        else range(op.arity()))

	def _do_repr4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Write translation to string for kind"""
		ops = self.symbols_kind.get(kind, ())

		# The repr function does not make sense in empty kinds
		# (but we write a dummy definition since others may refer to it)
		if not ops:
			lean.def_case('"<empty>"', '_')
			return

		for op in ops:
			# Skip non-constructor symbols if only_ctors is enabled
			if self.only_ctors and not is_ctor(op):
				continue

			op_name = f'{self.kinds[kind]}.{self.symbols[op]}'
			variables = make_variables('a', op.arity())
			call = self._make_call(op_name, variables)

			if op.arity() == 0:
				lean.def_case(f'"{op}"', op_name)
			else:
				parts = ' ++ ", " ++ '.join(f'({var}.repr)' for var in variables)
				lean.def_case(f'"{op}(" ++ {parts} ++ ")"', call)

	def _do_repr(self, lean: LeanWriter):
		"""Write conversions to string"""

		lean.newline()
		lean.comment('String conversion')

		# Name of the Lean string type
		lean_string = 'string' if self.lean_version == 3 else 'String'

		# Prefix notation is used (infix notation would be better...)
		for scc in self.kind_ordering:
			# Prepare a kind to kind name dictionary for _do_mutual_or_simple
			scc_ext = {k: self.kinds[k] for k in scc}

			lean.newline()
			self._do_mutual_or_simple(lean, scc_ext, '{}.repr', f'{{}} → {lean_string}',
			                          self._do_repr4kind, is_def=True)

		lean.newline()

		# The class has_repr allows showing elements of these types with #eval
		for kind in self.symbols_kind.keys():
			if self.lean_version == 3:
				lean.print(f'instance : has_repr {self.kinds[kind]} := '
				           f'⟨ {self.kinds[kind]}.repr ⟩')
			else:
				lean.print(f'instance : Repr {self.kinds[kind]} := '
				           f'⟨ λ x _ => Std.Format.text ({self.kinds[kind]}.repr x) ⟩')

	def _warn_special_ops(self):
		"""Warn about the use of special operators"""

		# Warn about special operators
		bool_hooks = frozenset(('SystemTrue', 'SystemFalse', 'BranchSymbol', 'EqualitySymbol'))
		specials = [(op, special) for op, special in maudext.get_special_ops(self.mod)
		            if special[0] not in bool_hooks]

		if specials:
			diag.warning(f'the Maude module contains {len(specials)} '
			             f'special operators like {specials[0][0]} whose behavior is not '
			             'equationally defined in Maude.')

	def _do_eqa4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare equality modulo structural axioms for a given kind"""

		kind_name = self.kinds[kind]

		# Equivalence relation constructors
		lean.inductive_ctor('refl {a}', f'{kind_name}.eqa a a')
		lean.inductive_ctor('symm {a b}', f'{kind_name}.eqa a b → {kind_name}.eqa b a')
		lean.inductive_ctor('trans {a b c}', f'{kind_name}.eqa a b → {kind_name}.eqa b c → {kind_name}.eqa a c')

		# Congruence axioms
		lean.comment('\tCongruence axioms for each operator')
		for op in filter(maude.Symbol.arity, self.symbols_kind.get(kind, ())):
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
				condition = (f'{self.kinds[mtype.kind()]}.has_sort {var} MSort.{self.sorts[mtype]}'
				             for var, mtype in zip(variables, domain)
				             if self._is_proper_sort(mtype))

				label = f'{name}_decl{subindex(k) if len(decls) > 1 else ""}'
				call = self._make_call(f'{kind_name}.{name}', variables)
				body = self._make_chain(*condition, f'{kind_name}.has_sort {call} MSort.{self.sorts[range_sort]}')

				lean.print(f'\t| {label} {args}: {body}')
				labels.append(label)

		return labels

	def _do_has_sort4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare the sort membership relation for given kind"""

		kind_name = self.kinds[kind]

		lean.begin_inductive(f'{kind_name}.has_sort', f'{kind_name} → MSort → Prop')
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
			variables = ' '.join(v.getVarName().lower() for v in maudext.get_variables_stmt(mb))
			variables = f' {{{variables}}}' if variables else ''

			lean.inductive_ctor(f'{label}{variables}', *premise,
			                    f'{kind_name}.has_sort {lhs} MSort.{self.sorts[mb.getSort()]}')

	def _do_eqe4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare equality modulo equations for a given kind"""

		kind_name = self.kinds[kind]

		lean.begin_inductive(f'{kind_name}.eqe', f'{kind_name} → {kind_name} → Prop')
		lean.inductive_ctor('from_eqa {a b}', f'{kind_name}.eqa a b → {kind_name}.eqe a b')
		lean.inductive_ctor('symm {a b}', f'{kind_name}.eqe a b → {kind_name}.eqe b a')
		lean.inductive_ctor('trans {a b c}', f'{kind_name}.eqe a b → {kind_name}.eqe b c → {kind_name}.eqe a c')

		# Congruence axioms
		lean.comment('\tCongruence axioms for each operator')
		for op in filter(maude.Symbol.arity, self.symbols_kind.get(kind, ())):
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
			variables = ' '.join(v.getVarName().lower() for v in maudext.get_variables_stmt(eq))
			variables = f' {{{variables}}}' if variables else ''

			lean.inductive_ctor(f'{label}{variables}', *premise, f'{kind_name}.eqe {lhs} {rhs}')

	def _do_equational_relations(self, lean: LeanWriter):
		"""Declare the equational relations"""

		lean.newline()
		lean.comment('Sort membership and equality modulo equations')
		lean.newline()

		lean.begin_mutual_inductive(f'{kind}.{rel}'
		                            for rel in ('has_sort', 'eqe')
		                            for kind in self.kinds.values())

		# Sort membership relation
		for kind in self.kinds:
			self._do_has_sort4kind(lean, kind)
			lean.newline()

		# Equational relation
		for kind in self.kinds:
			self._do_eqe4kind(lean, kind)
			lean.newline()

		lean.end_mutual()

		# Introduce notation (if desired)
		self._declare_notation(lean, 'has-sort-symbol', 'has_sort')
		self._declare_notation(lean, 'eqa-symbol', 'eqa')
		self._declare_notation(lean, 'eqe-symbol', 'eqe')

	def _do_rw_one4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare the one-step sequential rule rewrite relation for the given kind"""

		kind_name = self.kinds[kind]

		lean.begin_inductive(f'{kind_name}.rw_one', f'{kind_name} → {kind_name} → Prop')
		lean.inductive_ctor('eqe_left {a b c}',
		                    f'{kind_name}.eqe a b → {kind_name}.rw_one b c → {kind_name}.rw_one a c')
		lean.inductive_ctor('eqe_right {a b c}',
		                    f'{kind_name}.rw_one a b → {kind_name}.eqe b c → {kind_name}.rw_one a c')

		# A rewrite in a subterm is a rewrite in the whole term
		lean.comment('\tAxioms for rewriting inside subterms')
		for op in self.symbols_kind.get(kind, ()):
			op_name = self.symbols[op]
			variables = make_variables('a', op.arity())
			for i in self._rewritable_args(op):
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
			variables = ' '.join(v.getVarName().lower() for v in maudext.get_variables_stmt(rl))
			variables = f' {{{variables}}}' if variables else ''

			lean.inductive_ctor(f'{label}{variables}', *premise, f'{kind_name}.rw_one {lhs} {rhs}')

	def _do_rewriting_relations(self, lean: LeanWriter):
		"""Declare the rewriting relations"""

		lean.comment('Rewriting relations')
		lean.newline()

		lean.begin_mutual_inductive(f'{kind}.{rel}'
		                            for rel in ('rw_one', 'rw_star')
		                            for kind in self.kinds.values())

		# One-step relation
		for kind in self.kinds:
			self._do_rw_one4kind(lean, kind)
			lean.newline()

		# Transitive and reflective closure
		# (we could define as the reflexive and transitive closure by a definition,
		# but the one step relation may have mutual dependencies with this one)
		for kind, kind_name in self.kinds.items():
			lean.begin_inductive(f'{kind_name}.rw_star', f'{kind_name} → {kind_name} → Prop')
			lean.inductive_ctor('step {a b}', f'{kind_name}.rw_one a b → {kind_name}.rw_star a b')
			lean.inductive_ctor('refl {a b}', f'{kind_name}.eqe a b → {kind_name}.rw_star a b')
			lean.inductive_ctor('trans {a b c}', f'{kind_name}.rw_star a b → {kind_name}.rw_star b c → {kind_name}.rw_star a c')
			lean.newline()

		lean.end_mutual()

		# Introduce notation (if desired)
		self._declare_notation(lean, 'rw-one-symbol', 'rw_one')
		self._declare_notation(lean, 'rw-star-symbol', 'rw_star')

	def _do_simp4kind(self, lean: LeanWriter, kind: maude.Kind, simp_extra: list[str]):
		"""Declare the Lean simplifier attribute for the standard axioms"""

		# Definitions for the simplifier
		simp_labels = (
			# Implicit membership axioms (i.e. operator declarations)
			[f'has_sort.{label}' for label in self.impl_mb_axioms[kind]] +
			# Explicit membership axioms
			[f'has_sort.{label}' for mb, label in self.all_mbs.get(kind, ()) if not mb.isNonexec()] +
			# Equations
			[f'eqe.{label}' for eq, label in self.all_eqs.get(kind, ()) if not eq.isNonexec()] +
			# Derived definitions (with the derived-as-defs optimization)
			[self.symbols[op] for scc, _ in self.derived_defs for op, _ in scc
			 if op.getRangeSort().kind() == kind] +
			# Other declarations
			simp_extra)

		# Include structural axioms in the simplifier (if desired)
		if self.opts['with-axiom-simp']:
			for op, axioms in self.all_axioms.get(kind, ()):
				op_name = self.symbols[op]

				for axiom, *_ in axioms:
					if axiom != 'i':
						simp_labels.append(f'eqa.{op_name}_{self.AXIOM_NAMES[axiom]}')

		if simp_labels:
			lean.print('attribute [simp]', ' '.join(simp_labels))

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

		# Simplifier axioms
		self._do_simp4kind(lean, kind, simp_extra)

	def _do_rewriting_attrs4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare Lean attributes for the standard axiom of the rewriting relations"""

		lean.newline()
		lean.comment('Attributes for the Lean simplifier and machinery')

		lean.print('attribute [refl] rw_star.refl')
		lean.print('attribute [trans] rw_star.trans')

	def _do_equational_aliases4kind(self, lean: LeanWriter, kind: maude.Kind):
		"""Declare aliases for equational definitions for the given kind"""

		lean.comment('Aliases')

		for op, axioms in self.all_axioms.get(kind, ()):
			op_name = self.symbols[op]

			for axiom, *_ in axioms:
				if axiom != 'i':
					label = f'{op_name}_{self.AXIOM_NAMES[axiom]}'
					lean.print(f'def {label} := @eqa.{label}')

		# Implicit membership axioms
		for label in self.impl_mb_axioms.get(kind, ()):
			lean.print(f'def {label} := @has_sort.{label}')

		# Explicit membership axioms
		for _, label in self.all_mbs.get(kind, ()):
			lean.print(f'def {label} := @has_sort.{label}')

		# Congruence axioms
		for op in filter(maude.Symbol.arity, self.symbols_kind.get(kind, ())):
			op_name = self.symbols[op]
			lean.print(f'def eqa_{op_name} := @eqa.eqa_{op_name}')
			lean.print(f'def eqe_{op_name} := @eqe.eqe_{op_name}')

		# Equations
		for _, label in self.all_eqs.get(kind, ()):
			lean.print(f'def {label} := @eqe.{label}')

	def _do_lemmas(self, lean: LeanWriter):
		"""Introduce lemmas for the axioms"""

		lean.comment('Lemmas and aliases')

		# These variables are used to make lemmas compatible for both Lean 3 and 4
		lemma, congr_decl, refl_decl = 'lemma', '@[congr] ', '@[refl] ',
		lambda_sep, extension = ',', 'lean'

		if self.lean_version == 4:
			lemma, congr_decl, refl_decl = 'theorem', '', ''
			lambda_sep, extension = ' =>', 'lean4'

		# Write a generic congruence lemma for proving congruences
		lean.newline()
		lean.print(pkg_resources.read_text(data, f'generic_congr.{extension}'))

		for kind, kind_name in self.kinds.items():

			# They are put in their kind's namespace
			lean.begin_namespace(kind_name)

			# Axioms that will be added the simp attribute
			simp_axioms = []

			lean.comment('Sort membership lemmas')

			# Subsort relations
			for sort in map(kind.sort, range(1, kind.nrSorts())):
				for subsort in unique(sort.getSubsorts()):
					label = f'subsort_{self.sorts[subsort].lower()}_{self.sorts[sort].lower()}'
					lean.print(f'{lemma} {label} {{t : {kind_name}}} :',
					           f't{self.has_sort}MSort.{self.sorts[subsort]} →\n\t'
					           f't{self.has_sort}MSort.{self.sorts[sort]}',
					           ':= by apply has_sort.subsort; simp [subsort]')

					simp_axioms.append(label)

			lean.newline()
			lean.comment('Reflexivity and congruence lemmas')

			lean.print(f'{refl_decl}{lemma} eqe_refl (a : {kind_name}) : a{self.eqe}a := eqe.from_eqa eqa.refl')

			# Congruence axiom for the relations themselves
			lean.print(f'{lemma} eqa_congr {{a b c d : {kind_name}}} : a{self.eqa}b → c{self.eqa}d → '
			           f'(a{self.eqa}c) = (b{self.eqa}d)\n\t:= generic_congr @eqa.trans @eqa.trans @eqa.symm')
			lean.print(f'{lemma} eqe_congr {{a b c d : {kind_name}}} : a{self.eqe}b → c{self.eqe}d → '
			           f'(a{self.eqe}c) = (b{self.eqe}d)\n\t:= generic_congr @eqe.trans @eqe.trans @eqe.symm')
			lean.print(f'{lemma} eqa_eqe_congr {{a b c d : {kind_name}}} : a{self.eqa}b → c{self.eqa}d → '
			           f'(a{self.eqe}c) = (b{self.eqe}d)\n\t:= generic_congr '
			           f'(λ {{x y z}}{lambda_sep} (@eqe.trans x y z) ∘ (@eqe.from_eqa x y))\n\t\t'
			           f'(λ {{x y z h}}{lambda_sep} (@eqe.trans x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm')

			congr_axioms = ['eqa_congr', 'eqe_congr', 'eqa_eqe_congr']

			# Write shorter aliases for some definitions
			if self.opts['with-aliases']:
				lean.newline()
				self._do_equational_aliases4kind(lean, kind)

			# Activate the membership axioms for the Lean simplifier
			if self.opts['with-simp']:
				lean.newline()

				if self.lean_version == 3:
					self._do_equational_attrs4kind(lean, kind, simp_axioms, congr_axioms)
				else:
					self._do_simp4kind(lean, kind, simp_axioms)

			lean.end_namespace()

		if not self.opts['with-rules']:
			return

		lean.newline()
		lean.comment('Lemmas for the rewriting relation')

		# Write the generic infer_sub_star tactic (only for Lean 3 at the moment)
		if self.lean_version == 3:
			lean.print('\n' + pkg_resources.read_text(data, 'infer_sub_star.lean'))

		for kind, kind_name in self.kinds.items():
			lean.begin_namespace(kind_name)

			# Congruence lemmas with respect to =E and =A
			lean.comment('Congruence lemmas')

			lean.print(f'{congr_decl}{lemma} eqe_rw_one_congr {{a b c d : {kind_name}}} : a{self.eqe}b → c{self.eqe}d → '
			           f'(a{self.rw_one}c) = (b{self.rw_one}d)\n\t:= generic_congr @rw_one.eqe_left @rw_one.eqe_right @eqe.symm')
			lean.print(f'{congr_decl}{lemma} eqa_rw_one_congr {{a b c d : {kind_name}}} : a{self.eqa}b → c{self.eqa}d → '
			           f'(a{self.rw_one}c) = (b{self.rw_one}d)\n\t:= generic_congr '
			           f'(λ {{x y z}}{lambda_sep} (@rw_one.eqe_left x y z) ∘ (@eqe.from_eqa x y))\n\t\t'
			           f'(λ {{x y z h}}{lambda_sep} (@rw_one.eqe_right x y z h) ∘ (@eqe.from_eqa y z)) @eqa.symm')
			lean.print(f'{congr_decl}{lemma} eqe_rw_star_congr {{a b c d : {kind_name}}} : a{self.eqe}b → c{self.eqe}d → '
			           f'(a{self.rw_star}c) = (b{self.rw_star}d)\n\t:= generic_congr '
			           f'(λ {{x y z}}{lambda_sep} (@rw_star.trans x y z) ∘ (@rw_star.refl x y))\n\t\t'
			           f'(λ {{x y z h}}{lambda_sep} (@rw_star.trans x y z h) ∘ (@rw_star.refl y z)) @eqe.symm')
			lean.print(f'{congr_decl}{lemma} eqa_rw_star_congr {{a b c d : {kind_name}}} : a{self.eqa}b → c{self.eqa}d → '
			           f'(a{self.rw_star}c) = (b{self.rw_star}d)\n\t:= generic_congr '
			           f'(λ {{x y z}}{lambda_sep} (@rw_star.trans x y z) ∘ (@rw_star.refl x y) ∘ (@eqe.from_eqa x y))\n\t\t'
			           f'(λ {{x y z h}}{lambda_sep} (@rw_star.trans x y z h) ∘ (@rw_star.refl y z) ∘ (@eqe.from_eqa y z)) @eqa.symm')

			# Aliases for the rewrite rules
			if self.opts['with-aliases'] and kind in self.all_rls:
				lean.newline()
				lean.comment('Aliases for rewrite rules')
				for rl, label in self.all_rls.get(kind, ()):
					lean.print(f'def {label} := @rw_one.{label}')

			# Lean 4 does not currently support the refl and trans attributes
			# and we have not adapted the infer_sub_star metaproof to Lean 4
			if self.lean_version == 4:
				lean.end_namespace()
				continue

			# Attributes (even without with-simp, since they are required for the lemmas)
			self._do_rewriting_attrs4kind(lean, kind)

			# Subterm rewriting lemmas for =>*
			lean.newline()
			lean.comment('Lemmas for subterm rewriting with =>*')

			for op in self.symbols_kind.get(kind, ()):
				op_name = self.symbols[op]
				variables = make_variables('a', op.arity())
				for i in self._rewritable_args(op):
					args = [f'{var}' if j != i else 'a b' for j, var in enumerate(variables)]
					args = self._make_collapsed_args(op, args)
					label = f'sub_{op_name}{subindex(i) if op.arity() > 1 else ""}'
					lean.print(f'{lemma} rw_star_{label} {args} : a{self.rw_star}b →\n\t\t'
					           f'{self._make_call(op_name, replace(variables, i, "a"))}{self.rw_star}'
					           f'{self._make_call(op_name, replace(variables, i, "b"))} := by '
					           f'infer_sub_star ``(rw_one.{label}) ``(eqe.eqe_{op_name})')

			lean.end_namespace()

	def translate(self, lean: LeanWriter):
		"""Do the translation"""

		# By default, everything is inserted into the Maude namespace
		outermost_namespace = self.opts['outermost-namespace']

		if outermost_namespace:
			lean.print('namespace', outermost_namespace)

		if len(self.mod.getSorts()) == 0:
			lean.print('\t-- Empty module\nend Maude')
			return

		self._warn_special_ops()

		self._do_sorts(lean)
		self._do_symbols(lean)
		if self.opts['with-sort2kind']:
			self._do_kind_assignment(lean)
		if self.opts['with-ctor-predicate']:
			self._do_ctor_only(lean)

		self._do_derived_defs(lean)

		self._do_eqa(lean)
		self._do_equational_relations(lean)

		if self.opts['with-rules']:
			self._do_rewriting_relations(lean)

		if self.opts['with-lemmas']:
			self._do_lemmas(lean)

		if self.opts['with-repr']:
			self._do_repr(lean)

		if outermost_namespace:
			lean.print('\nend', outermost_namespace)
