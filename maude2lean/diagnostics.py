#
# Functions for showing diagnostics
#

import os
import sys

# Prefixes for the messages
_warning_prefix = 'Warning:'
_info_prefix = 'Info:'

# Use color if the standard error stream is a terminal
if os.isatty(sys.stderr.fileno()):
	_warning_prefix = '\x1b[33;1mWarning:\x1b[0m'
	_info_prefix = '\x1b[34;1mInfo:\x1b[0m'


def warning(msg: str):
	"""Print a warning"""

	print(_warning_prefix, msg, file=sys.stderr)


def info(msg: str):
	"""Show an informative message"""

	print(_info_prefix, msg, file=sys.stderr)
