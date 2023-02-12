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
