#
# Extensions on the Maude library
#

import maude


def get_structural_axioms(module: maude.Module):
	"""Get the structural axioms of a module"""

	# Kind-indexed dictionary of (operator, axioms) tuples
	all_axioms = {}

	for op in module.getSymbols():
		# List of axioms (indicated by a single letter, except for identity
		# axioms that come with the object-level identity element term)
		axioms = []

		if op.hasAttr(maude.OP_COMM):
			axioms.append('c')
		if op.hasAttr(maude.OP_ASSOC):
			axioms.append('a')
		if op.hasAttr(maude.OP_IDEM):
			axioms.append('d')
		if op.hasAttr(maude.OP_LEFT_ID):
			flag = 'i' if op.hasAttr(maude.OP_RIGHT_ID) else 'l'
			axioms.append((flag, op.getIdentity()))
		elif op.hasAttr(maude.OP_RIGHT_ID):
			axioms.append(('r', op.getIdentity()))

		if axioms:
			all_axioms[op] = axioms

	return all_axioms


def get_special_ops(module: maude.Module):
	"""Get the special operators of the module"""

	# List of (operator, id-hook) tuples
	specials = []

	for op in module.getSymbols():
		if hooks := op.getIdHooks():
			specials.append((op, hooks[0]))

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


class FakeSet(dict):
	"""Set implemented using a dictionary that preserves insertion order"""

	def add(self, elem):
		self[elem] = None


def get_variables_stmt(stmt):
	"""Get the variables in a statement"""

	# Use a modified dictionary instead a set because it preserves
	# the insertion order, and we want to process variables in the
	# order they appear in the term. The function user will not
	# probably notice the difference.
	varset = FakeSet()

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
