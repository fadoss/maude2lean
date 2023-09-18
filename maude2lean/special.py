#
# Support for some special Maude operators
#

import maude


class FakeEquation:
	"""Fake equation for special operators"""

	def __init__(self, lhs, rhs, label=None, condition=()):
		self.label = label
		self.lhs = lhs
		self.rhs = rhs
		self.condition = condition

	def getLhs(self):
		return self.lhs

	def getRhs(self):
		return self.rhs

	def getLabel(self):
		return self.label

	def isNonexec(self):
		return False

	def isOwise(self):
		return False

	def getCondition(self):
		return self.condition

	def __repr__(self):
		if self.condition:
			cond_str = r' /\ '.join(map(str, self.condition))
			return f'ceq {self.lhs} = {self.rhs} if {cond_str} [fake] .'
		else:
			return f'eq {self.lhs} = {self.rhs} [fake] .'


def special_equations(mod: maude.Module):
	"""Generate equations for some polymorphic operators in a module"""

	eqs = []

	for op in mod.getSymbols():
		if not (hooks := op.getIdHooks()):
			continue

		kind = op.getRangeSort().kind()

		# if_then_else_fi
		if hooks[0][0] == 'BranchSymbol':
			lvar = mod.parseTerm(f'L:{kind}', kind)
			rvar = mod.parseTerm(f'R:{kind}', kind)
			terms = op.getTermHooks()

			eqs.append(FakeEquation(op(terms['1'], lvar, rvar), lvar, label='itet'))
			eqs.append(FakeEquation(op(terms['2'], lvar, rvar), rvar, label='itef'))

		# ==_ and _=/=_
		elif hooks[0][0] == 'EqualitySymbol':
			lvar = mod.parseTerm(f'L:{kind}', kind)
			rvar = mod.parseTerm(f'R:{kind}', kind)
			eqcond = maude.EqualityCondition(lvar, rvar)
			rhs = op.getTermHooks()['equalTerm']

			eqs.append(FakeEquation(op(lvar, rvar), rhs, condition=(eqcond,)))

	return eqs


def find_bool(mod: maude.Module, lean_version=3):
	"""Find the Bool sort and its symbols"""

	true_symb = None
	false_symb = None
	translate = {}

	# First pass to detect true, false, and if_then_else_fi
	for op in mod.getSymbols():
		if not (hooks := op.getIdHooks()):
			continue

		if hooks[0][0] == 'SystemTrue':
			true_symb = op

		elif hooks[0][0] == 'SystemFalse':
			false_symb = op

	# We should now find the derived symbols and equations
	if true_symb is not None:
		# Translate the Boolean constants
		translate[true_symb] = 'tt' if lean_version == 3 else 'true'
		translate[false_symb] = 'ff' if lean_version == 3 else 'false'

		bool_kind = true_symb.getRangeSort().kind()

		# Since Boolean operators are not special, their
		# detection is somehow heuristic

		for op in mod.getSymbols():
			hooks = op.getIdHooks()

			# Lean's cond is used instead of if_then_else_fi
			if hooks and hooks[0][0] == 'BranchSymbol':
				translate[op] = '(cond {} {} {})'

			# This is not one of the operators we are looking for
			elif (op.arity() == 0 or op.getRangeSort().kind() != bool_kind
			      or op.domainKind(0) != bool_kind):
				continue

			name, prec = str(op), op.getPrec()

			# All are binary operators except not
			if op.arity() == 1 and (name == 'not_' or prec == 53):
				translate[op] = '(¬ {})'

			elif (op.arity() == 2 and op.domainKind(1) == bool_kind
			      and op.isAssoc() and op.hasAttr(maude.OP_COMM)):
				if name == '_and_' or prec == 55:
					translate[op] = '({} && {})'
				elif name == '_or_' or prec == 59:
					translate[op] = '({} || {})'

	return true_symb, false_symb, translate
