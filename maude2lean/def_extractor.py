#
# Extract Lean definitions from derived Maude operators
#

import sys
from collections import Counter

import maude

from . import diagnostics as diag
from .graph import Graph
from .maudext import is_ctor


class ComplStatus:
	"""Result of the equation completeness check"""

	def __init__(self, msg=None, closed_kinds=None):
		self.msg = msg
		self.closed_kinds = closed_kinds

	def __bool__(self):
		return self.msg is None

	def __str__(self):
		return self.msg


def preorder(term: maude.Term):
	"""Get the subterms of the given term in preorder"""

	stack = [iter((term,))]

	while stack:
		t = next(stack[-1], None)

		if not t:
			stack.pop()
		else:
			yield t

			if t.symbol().arity() > 0:
				stack.append(iter(t.arguments()))


def is_linear(term: maude.Term):
	"""Check whether a given term is linear (each variable occurs at most once)"""

	seen_vars = set()

	for t in preorder(term):
		if t.isVariable():
			if t in seen_vars:
				return False

			seen_vars.add(t)

	return True


def is_pattern(term: maude.Term):
	"""Check whether a given term is a pattern (made out of constructor terms)"""

	for t in preorder(term):
		if not t.isVariable() and not is_ctor(t.symbol()):
			return False

	return True


def complete(eqs: list, ctors: dict, wks: dict):
	"""Check whether the given set of equations is complete"""

	if not eqs:
		return ComplStatus('no equations')

	# (1) Equations are unconditional
	if any(eq.getCondition() for eq in eqs):
		return ComplStatus('there is a conditional equation')

	# The LHS of equations
	lhss = [eq.getLhs() for eq in eqs]

	# (2) Left-hand sides are linear
	for lhs in lhss:
		if not is_linear(lhs):
			return ComplStatus(f'pattern {lhs} is not linear')

	# (3) Left-hand sides are patterns
	for lhs in lhss:
		for arg in lhs.arguments():
			if not is_pattern(arg):
				return ComplStatus(f'term {lhs} is not a pattern')

	# (4) Patterns cover all cases
	problems = [tuple(tuple(lhs.arguments()) for lhs in lhss)]

	if not problems[0][0] and len(problems[0]) > 1:
		return ComplStatus('equations are redundant')

	# Kinds for which a explicit case distinction occurs
	closed_kinds = set()

	while problems:
		cases = problems.pop()
		symbol_map, var_cases, none_cases = {}, [], []

		# Skip trivial cases
		if not cases[0]:
			continue

		# Number of constructors in the next argument kind
		kind = cases[0][0].getSort().kind()
		num_ctors = len(ctors[kind])

		# Group cases by top symbol of the first argument
		for case in cases:
			if case[0] is None:
				none_cases.append(case[1:])
			elif case[0].isVariable():
				var_sort = case[0].getSort()
				var_kind = var_sort.kind()

				# If the variable belongs to a proper subsort, it is an error
				if var_sort != wks.get(var_kind) and var_sort != var_kind.sort(0):
					return ComplStatus(f'variable {case[0].getVarName()} of proper subsort {var_sort}')

				var_cases.append(case[1:])
			else:
				symbol_map.setdefault(case[0].symbol(), []).append(case)

		# Check whether all constructors are covered
		if len(symbol_map) < num_ctors:
			if not var_cases:
				return ComplStatus('patterns are not exhaustive')
			# If there is a variable and some but not all patterns, what follows the
			# variable should not be exhaustive or it will be redundant with the patterns,
			# but then it will be not exhaustive for the missing constructors
			elif len(symbol_map) > 0:
				return ComplStatus('patterns are not exhaustive or redundant')

		# Closed case distinction
		if not var_cases:
			closed_kinds.add(kind)

		# In the last argument, check whether there are no duplicities
		if len(cases[0]) == 1 and (any(len(opts) > 1 for opts in symbol_map.values())
		                           or symbol_map and var_cases)	:
			return ComplStatus('patterns are redundant')

		var_cases += none_cases

		# Build problems
		if not symbol_map:
			problems.append(var_cases)
			continue

		for symb, cases in symbol_map.items():
			arity = symb.arity()

			if arity == 0:
				cases = [case[1:] for case in cases]
				problems.append(cases + var_cases)
			else:
				new_var_cases = [(None, ) * arity + case for case in var_cases]
				cases = [tuple(case[0].arguments()) + case[1:] for case in cases]
				problems.append(cases + new_var_cases)

	return ComplStatus(closed_kinds=closed_kinds)


def index_equations(m: maude.Module):
	"""Index equations by the top symbol of the LHS"""

	equations = {}

	for eq in m.getEquations():
		equations.setdefault(eq.getLhs().symbol(), []).append(eq)

	return equations


def index_constructors(m: maude.Module):
	"""Index constructor symbols by kind"""

	ctors, non_ctors = {}, Counter()

	for symb in m.getSymbols():
		# Skip the pseudosymbol used for variables
		if str(symb) == str(symb.getRangeSort()):
			continue

		kind = symb.getRangeSort().kind()

		if is_ctor(symb):
			ctors.setdefault(kind, []).append(symb)
		else:
			non_ctors[kind] += 1

	return ctors, non_ctors


def whole_kind_sorts(m: maude.Module):
	"""Computes a dictionary from kinds to their whole-kind sorts (if any)"""

	wks = {}

	for kind in m.getKinds():
		if kind.errorFree() and kind.nrMaximalSorts() == 1:
			wks[kind] = kind.sort(1)

	return wks


def find_used(term: maude.Term, symbs: set, used: set):
	"""Find uses of the given symbols in a term"""

	# Whether other non-constructor terms are used
	used_nonctor = False

	for t in preorder(term):
		symb = t.symbol()
		if symb in symbs:
			used.add(symb)
		elif not used_nonctor and not is_ctor(symb):
			used_nonctor = True

	return used_nonctor


def get_dependencies(eqs: list, symbs: set):
	"""Get dependencies of the set of derived operators"""

	used, used_nonctor = set(), False

	for eq in eqs:
		if find_used(eq.getRhs(), symbs, used):
			used_nonctor = True

	return used, used_nonctor


def get_simple_derived_symbols(m: maude.Module, cover_nonctor=True, verbose=False):
	"""Obtain a list of symbols that can be translated to Lean definitions"""

	# Index equations by top symbol
	eqs = index_equations(m)

	# Index constructors by kind and get the number of non-constructors
	ctors, non_ctors = index_constructors(m)

	# Obtain the whole-kind sort for each kind
	wks = whole_kind_sorts(m)

	symbs = []

	# Check every non-constructor symbol with equations
	# using the complete function
	for symb in m.getSymbols():
		if not is_ctor(symb) and (symb_eqs := eqs.get(symb)):
			status = complete(symb_eqs, ctors, wks)

			if not status:
				if verbose:
					diag.info(f'the definition of {symb} is not '
					          f'convertible to Lean: {status}.')
			else:
				non_ctors[symb.getRangeSort().kind()] -= 1
				symbs.append((symb, status.closed_kinds))

	# Eliminate definitions doing a exhaustive case distinction on a kind that
	# contains non-constructor symbols that cannot be transformed to definitions
	# (otherwise, the definition will not be exhaustive on those)
	if cover_nonctor:
		# Multiple passes are required since eliminating a definition from
		# a type may involve other definitions including that type
		kinds_changed = True
		msg = 'exhaustive case distinction on kind with non-constructor symbols'
		while kinds_changed:
			# The affected entries are removed from the list
			removed, kinds_changed = 0, False
			for i in range(len(symbs)):
				op, ks = symbs[i - removed]
				if any(non_ctors[k] for k in ks):
					diag.info(f'the definition of {op} is not '
					          f'convertible to Lean: {msg}.')
					del symbs[i - removed]
					removed += 1
					# Check whether the kind of op is affected
					kind = op.getRangeSort().kind()
					if not non_ctors[kind]:
						kinds_changed = True
					non_ctors[kind] += 1

	# Build the dependency graph between definitions to group those mutually dependent
	graph = Graph()
	symbs_set, used_nonctor = {op for op, *_ in symbs}, {}
	recursive = False

	for op, _ in symbs:
		used, used_nonctor[op] = get_dependencies(eqs[op], symbs_set)
		graph.add_vertex(op)
		for symb in used:
			graph.add_edge(op, symb)
			if op == symb:
				recursive = True

	# Get the topological ordering of the strongly-connected components
	sccs = graph.topological_scc()

	# We return a list of groups of mutually recursive definitions (ops, dep)
	# where ops is a sequence of pairs of symbols with their equations and dep
	# tells whether they depend on non-constructor symbols without definition
	return [(tuple((op, eqs[op]) for op in scc),
	         any(used_nonctor[op] for op in scc)) for scc in sccs], recursive
