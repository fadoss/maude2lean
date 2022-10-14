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


def to_lean(module_name: str, spec: dict, ofile, verbose=False):
	"""Convert a Maude module to a Lean specification"""

	from . import Maude2Lean
	from .lean import LeanWriter

	module = maude.getModule(module_name) if module_name else maude.getCurrentModule()

	if module is None:
		print(f'Error: the module {module_name} is not valid or does not exist.')
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
	parser.add_argument('-o', help='Output file name')

	args = parser.parse_args()

	maude.init()

	spec = handle_input_file(args.source)

	if spec is None:
		return 1

	# Take module from the command line or otherwise from the specification
	module = args.module if args.module else spec.get('module')

	# Take output file name from the command line
	output_file = open(args.o, 'w') if args.o else sys.stdout

	return to_lean(module, spec, output_file, args.verbose)


if __name__ == '__main__':
	sys.exit(main())
