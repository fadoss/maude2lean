#
# Entry point of the Maude to Lean translator
#

import os
import sys
import maude


def handle_input_file(filename: str):
	"""Handle the input file"""

	basedir = os.path.dirname(filename)

	if filename.endswith('.json'):
		import json
		with open(filename) as json_file:
			spec = json.load(json_file)

	elif filename.endswith('.yaml'):
		try:
			import yaml
			with open(filename) as yaml_file:
				spec = yaml.safe_load(yaml_file)

		except ImportError:
			print('The yaml package is not installed. Please convert the YAML to '
			      'JSON or install it with pip install pyaml.')
			return None

	elif filename.endswith('.toml'):
		try:
			import tomllib
			with open(filename) as toml_file:
				spec = tomllib.load(toml_file)

		except ImportError:
			print('The tomllib package is not available. Please update Python to '
			      'its 3.11 version.')

	elif filename.endswith('.dict'):
		import ast

		with open(filename) as dict_file:
			spec = ast.literal_eval(dict_file.read())

	else:
		spec = {'source': filename}
		basedir = '.'

	# Load the files in the input specification
	# (either a single one or a list of them)
	source_files = spec.get('source')

	if source_files:
		source_files = source_files if isinstance(source_files, list) else (source_files,)

		for source_file in source_files:
			# Relative path are referred by default to the directory of the input file
			path_from_base = os.path.join(basedir, source_file)
			source_file = path_from_base if os.path.exists(path_from_base) else source_file

			if not maude.load(source_file):
				return None

	return spec


def to_lean(spec: dict, ofile, verbose=False):
	"""Convert a Maude module to a Lean specification"""

	from . import Maude2Lean
	from .lean import LeanWriter

	module_name = spec.get('module')
	module = maude.getModule(module_name) if module_name else maude.getCurrentModule()

	if module is None:
		print(f'Error: the module {module_name} is not valid or does not exist.',
		      file=sys.stderr)
		return 1

	# Use the metamodule as the translation module if provided
	if metamodule := spec.get('metamodule'):
		if (module_term := module.parseTerm(metamodule)) is None:
			print(f'Error: the given metamodule term cannot be parsed in {module_name}.',
			      file=sys.stderr)
			return 1

		if (module := maude.downModule(module_term)) is None:
			print(f'Error: the given metamodule ({metamodule}) is not valid.',
			      file=sys.stderr)
			return 1

	trans = Maude2Lean(module, spec, verbose=verbose)
	lean = LeanWriter(ofile, spec)

	trans.translate(lean)

	return 0


def main():
	import argparse

	parser = argparse.ArgumentParser(description='Translate Maude specifications to Lean programs')

	parser.add_argument('source', help='Source file')
	parser.add_argument('module', help='Module', nargs='?')
	parser.add_argument('--verbose', '-v', help='Show additional informative messages', action='store_true')
	parser.add_argument('--no-advise', help='Disable Maude advisory messages', dest='advise', action='store_false')
	parser.add_argument('-o', help='Output file name')

	args = parser.parse_args()

	maude.init(advise=args.advise)

	spec = handle_input_file(args.source)

	if spec is None:
		return 1

	# The command-line module overwrites the specification one
	if args.module:
		# The argument is seen as a metamodule if there is a space
		mtype = 'metamodule' if ' ' in args.module else 'module'
		spec[mtype] = args.module

	# Take output file name from the command line
	output_file = open(args.o, 'w') if args.o else sys.stdout

	return to_lean(spec, output_file, args.verbose)


if __name__ == '__main__':
	sys.exit(main())
