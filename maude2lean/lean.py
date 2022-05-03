#
# Lean 3 generator helper
#

import sys
from io import StringIO


class LeanWriter:
	"""Helper class for writing Lean 3 files"""

	def __init__(self, out=sys.stdout, opts: dict = None):
		self.out = out
		self.opts = opts if opts is not None else {}
		self.namespace_stack = []

	def _write(self, msg: str):
		"""Write an indented line"""
		self.out.write('\t' * len(self.namespace_stack) + msg)

	def comment(self, text: str):
		"""Single line comment"""
		for line in text.split('\n'):
			tabs, line = len(line), line.lstrip('\t')
			tabs = '\t' * (tabs - len(line))
			self._write(f'{tabs}-- {line}\n')

	def decl_notation(self, name: str, prio: int, value: str):
		"""Notation declaration"""
		self._write(f'infix ` {name} `:{prio} := {value}\n')

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
		self._write(f'\t| {name}{signature}\n')

	def end_inductive(self):
		"""Inductive type declaration tail"""
		pass

	def def_case(self, lhs: str, rhs: str):
		"""Inductive definition case"""
		self._write(f'\t| {lhs} := {rhs}\n')

	def begin_def(self, name: str, *types: str):
		"""Inductive definition header"""
		self._write(f'def {name} : {" → ".join(types)}\n')

	def end_def(self):
		"""Inductive definition tail"""
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
			# Letterlike symbols
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
