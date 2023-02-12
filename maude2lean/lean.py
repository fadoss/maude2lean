#
# Lean 3 generator helper
#

import sys
from io import StringIO
from typing import Iterable


class LeanWriter:
	"""Base class for writing Lean files"""

	TAB = '\t'  # Indentation text (Lean 4 only admit spaces)

	def __init__(self, out=sys.stdout, opts: dict = None):
		self.out = out
		self.opts = opts if opts is not None else {}
		self.namespace_stack = []

	def _write(self, msg: str):
		"""Write an indented line"""
		self.out.write(self.TAB * len(self.namespace_stack)
		               + msg.replace('\t', self.TAB))

	def comment(self, text: str):
		"""Single line comment"""
		for line in text.split('\n'):
			tabs, line = len(line), line.lstrip('\t')
			tabs = self.TAB * (tabs - len(line))
			self._write(f'{tabs}-- {line}\n')

	def decl_constants(self, ctype: str, *names: str):
		"""Constant declaration"""
		kwd = 'constant' if len(names) == 1 else 'constants'
		self._write(f'{kwd} {" ".join(names)} : {ctype}\n')

	def decl_variables(self, ctype: str, *names: str, implicit=True):
		"""Variable declaration"""
		kwd = 'variable' if len(names) == 1 else 'variables'
		if implicit:
			self._write(f'{kwd} {{{" ".join(names)} : {ctype}}}\n')
		else:
			self._write(f'{kwd} {" ".join(names)} : {ctype}\n')

	def begin_inductive(self, name: str, ctype: str = 'Type'):
		"""Inductive type declaration header"""
		sign = f': {ctype}' if ctype != 'Type' else ''
		self._write(f'inductive {name}{sign}\n')

	def inductive_ctor(self, name: str, *sign: str):
		"""Inductive type constructor"""
		signature = ' : ' + ' → '.join(sign) if sign else ''
		self._write(f'{self.TAB}| {name}{signature}\n')

	def end_inductive(self):
		"""Inductive type declaration tail"""
		pass

	def begin_def(self, name: str, *types: str, computable=True):
		"""Inductive definition header"""
		self._write(f'def {name} : {" → ".join(types)}\n')

	def end_def(self):
		"""Inductive definition tail"""
		pass

	def end_mutual(self):
		"""Mutual inductive definition tail"""
		pass

	def begin_namespace(self, name: str):
		"""Open a namespace"""
		self._write(f'\nnamespace {name}\n')
		self.namespace_stack.append(name)

	def end_namespace(self):
		"""Close a namespace"""
		name = self.namespace_stack.pop()
		self._write(f'end {name}\n')

	def newline(self):
		"""Print a newline (without indentation)"""
		self.out.write('\n')

	def print(self, *text):
		"""Print free text"""
		with StringIO() as buffer:
			print(*text, file=buffer)

			for k, line in enumerate(buffer.getvalue().split('\n')):
				if k:
					self.out.write('\n')
				if line:
					self._write(line)

	@staticmethod
	def allowed_char(c: str, first=False):
		"""Whether a character is allowed in a Lean identifier"""
		n = ord(c)
		return (
			# Latin letters
			ord('A') <= n <= ord('Z') or
			ord('a') <= n <= ord('z') or
			# Greek and coptic letters
			(0x370 <= n <= 0x3ff and c not in 'λΠΣ') or
			# Letter-like symbols
			(0x2100 <= n <= 0x214f) or
			# Low line
			c == '_' or
			# Except for the first letter
			not first and (
				# Decimal digit
				ord('0') <= n <= ord('9') or
				# Apostrophe
				c in "'" or
				# Subscripts
				ord('₀') <= n <= ord('₉')
			)
		)


class Lean3Writer(LeanWriter):
	"""Helper class for writing Lean 3 files"""

	def __init__(self, *args, **kwargs):
		super().__init__(*args, **kwargs)
		self.is_mutual = False

	def begin_mutual_inductive(self, names: Iterable[str]):
		"""Mutual inductive definition header"""
		self._write(f'mutual inductive {", ".join(names)}\n')
		self.is_mutual = True

	def begin_mutual_def(self, names: Iterable[str], computable=True):
		"""Mutual inductive definition header"""
		non_comp = '' if computable else 'noncomputable '
		self._write(f'{non_comp}mutual def {", ".join(names)}\n')
		self.is_mutual = True

	def end_mutual(self):
		"""Mutual inductive definition tail"""
		self.is_mutual = False

	def def_case(self, rhs: str, *lhs: str):
		"""Inductive definition case"""
		self._write(f'{self.TAB}| {" ".join(lhs)} := {rhs}\n')

	def begin_def(self, name: str, *types: str, computable=True):
		"""Inductive definition header"""
		kywd = 'with' if self.is_mutual else ('def' if computable else 'noncomputable def')
		self._write(f'{kywd} {name} : {" → ".join(types)}\n')

	def begin_inductive(self, name: str, ctype: str = 'Type'):
		"""Inductive type declaration header"""
		kywd = 'with' if self.is_mutual else 'inductive'
		sign = f' : {ctype}' if ctype != 'Type' else ''
		self._write(f'{kywd} {name}{sign}\n')

	def decl_notation(self, name: str, prio: int, value: str):
		"""Notation declaration"""
		# Lean 3.50.3 requires giving names to notation declarations
		# when the same syntax is used twice (this breaks older versions)
		notation_name = value.replace('.', '_')
		self._write(f'infix (name := {notation_name}) ` {name} `:{prio} := {value}\n')


class Lean4Writer(LeanWriter):
	"""Helper class for writing Lean 4 files"""

	# Lean 4 does not admit tabs, so we use 2 spaces
	TAB = '  '

	def begin_mutual_inductive(self, names: Iterable[str]):
		"""Mutual inductive definition header"""
		self._write('mutual\n')
		self.namespace_stack.append(None)

	def begin_mutual_def(self, names: Iterable[str], computable=None):
		"""Mutual inductive definition header"""
		self._write('mutual\n')
		self.namespace_stack.append(None)

	def end_mutual(self):
		"""Mutual inductive definition tail"""
		self.namespace_stack.pop()
		self._write('end\n')

	def begin_def(self, name: str, *types: str, computable=True):
		"""Inductive definition header"""
		super().begin_def(name, *types)
		# Definitions for multiple arguments are not for Lean 4
		if len(types) > 2:
			vs = tuple(f'a{k}' for k in range(len(types) - 1))
			self._write(f':= fun {" ".join(vs)} => '
			            f'match ({", ".join(vs)}) with\n')

	def def_case(self, rhs: str, *lhs: str):
		"""Inductive definition case"""
		# Multiple arguments are matched as a tuple
		lhs_str = lhs[0] if len(lhs) == 1 else f'({", ".join(lhs)})'
		self._write(f'{self.TAB}| {lhs_str} => {rhs}\n')

	def decl_notation(self, name: str, prio: int, value: str):
		"""Notation declaration"""
		self._write(f'infix:{prio} " {name} " => {value}\n')
