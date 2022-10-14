#
# Extensions on the Maude library
#

import maude


class MetalevelUtil:
	"""Useful functions relying on the metalevel"""

	def __init__(self):
		self.ml = maude.getModule('META-LEVEL')

	@staticmethod
	def _iterable_term(term: maude.Term, empty: str, join: str):
		"""Iterate over the elements of a list/set term"""
		top_symbol = str(term.symbol())

		if top_symbol == empty:
			return ()

		if top_symbol != join:
			return term,

		return term.arguments()

	@staticmethod
	def _strip_kind(sort_name: str):
		"""Get a plain sort name from any sort including error sorts"""

		if sort_name.startswith('`['):
			return sort_name[2:-2].split('`,', maxsplit=1)[0]

		return sort_name

	def _find_symbol(self, op: maude.Term, module: maude.Module):
		"""Find a symbol from its metadeclaration"""

		name, domain, range_s, _ = op.arguments()

		domain = [self._strip_kind(str(ty)[1:]) for ty in
		          self._iterable_term(domain, 'nil', '__')]

		# Polymorphs are omitted
		if 'Universal' in domain:
			return None

		domain = tuple(module.findSort(ty).kind() for ty in domain)
		range_s = module.findSort(self._strip_kind(str(range_s)[1:])).kind()

		return module.findSymbol(str(name)[1:], domain, range_s)

	def structural_axioms(self, module: maude.Module):
		"""Get the structural axioms of a module"""

		meta_ops = self.ml.parseTerm(f"upOpDecls('{str(module)}, true)")
		meta_ops.reduce()

		# Kind-indexed dictionary of (operator, axioms) tuples
		all_axioms = {}

		for op in self._iterable_term(meta_ops, 'none', '__'):
			symbol = self._find_symbol(op, module)

			# Polymorphs are not considered
			if not symbol:
				continue

			*_, attrs = op.arguments()

			# List of axioms (indicated by a single letter, except for identity
			# axioms that come with the object-level identity element term)
			axioms = []

			for attr in self._iterable_term(attrs, 'none', '__'):
				attr_name = str(attr.symbol())

				if attr_name == 'comm':
					axioms.append('c')
				elif attr_name == 'assoc':
					axioms.append('a')
				elif attr_name == 'idem':
					axioms.append('d')
				elif attr_name.endswith('id'):
					# Identity attributes take a term as parameter
					arg = module.downTerm(next(attr.arguments()))
					# We identify them by l, r, and i
					axioms.append((attr_name[0], arg))

			if axioms:
				all_axioms[symbol] = axioms

		return all_axioms

	def special_ops(self, module: maude.Module):
		"""Get the special operators of the module"""

		meta_ops = self.ml.parseTerm(f"upOpDecls('{str(module)}, true)")
		meta_ops.reduce()

		# List of (operator, id-hook) tuples
		specials = []

		for op in self._iterable_term(meta_ops, 'none', '__'):
			symbol = self._find_symbol(op, module)
			*_, attrs = op.arguments()

			if not symbol:
				continue

			for attr in self._iterable_term(attrs, 'none', '__'):
				attr_name = str(attr.symbol())

				if attr_name == 'special':
					hook_id = None

					for clause in self._iterable_term(next(attr.arguments()), 'nil', '__'):
						if str(clause.symbol()) == 'id-hook':
							name, _ = clause.arguments()
							hook_id = str(name)[1:]
							break

					specials.append((symbol, hook_id))

		return specials


def get_variables(term: maude.Term, varset: set[maude.Term]):
	"""Get the variables of a term"""

	if term.isVariable():
		varset.add(term)
	else:
		for arg in term.arguments():
			get_variables(arg, varset)


def get_variables_cfragment(fragment: maude.ConditionFragment, varset: set[maude.Term]):
	"""Get variables in a condition fragment"""
	get_variables(fragment.getLhs(), varset)

	if not isinstance(fragment, maude.SortTestCondition):
		get_variables(fragment.getRhs(), varset)


def get_variables_condition(condition: maude.Condition, varset: set[maude.Term]):
	"""Get the variables in a condition"""

	for frag in condition:
		get_variables_cfragment(frag, varset)


def get_variables_stmt(stmt):
	"""Get the variables in a statement"""
	varset = set()

	# Variables in the left- and right-hand side (if any)
	get_variables(stmt.getLhs(), varset)

	if hasattr(stmt, 'getRhs'):
		get_variables(stmt.getRhs(), varset)

	# Variables in the condition
	get_variables_condition(stmt.getCondition(), varset)

	return varset


def is_ctor(symb: maude.Symbol):
	"""Whether a symbol is a constructor"""

	# In principle, the constructor flag is specific to a declaration
	# (i.e. a symbol can be a constructor for some argument sorts and
	# not for others) but we do not make that distinction
	return any(decl.isConstructor() for decl in symb.getOpDeclarations())
