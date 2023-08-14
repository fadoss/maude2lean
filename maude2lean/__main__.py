#
# Entry point of the Maude to Lean translator
#

import importlib.resources
import json
import os
import sys

import maude

# Static files included in the package
data_root = importlib.resources.files(__package__) / 'data'


def handle_input_files(defaults: dict, filenames: list[str]):
	"""Handle the input files"""

	spec, spec_files, sources = defaults, [], []

	for filename in filenames:
		is_maude_file = False

		if filename.endswith('.json'):
			import json
			with open(filename) as json_file:
				spec |= json.load(json_file)

		elif filename.endswith('.yaml'):
			try:
				import yaml
				with open(filename) as yaml_file:
					spec |= yaml.safe_load(yaml_file)

			except ImportError:
				print('The yaml package is not installed. Please convert the YAML to '
				      'JSON or install it with pip install pyaml.')
				return None

		elif filename.endswith('.toml'):
			try:
				import tomllib
				with open(filename, 'rb') as toml_file:
					spec |= tomllib.load(toml_file)

			except ImportError:
				print('The tomllib package is not available. Please update Python to '
				      'its 3.11 version.')

		elif filename.endswith('.dict'):
			import ast

			with open(filename) as dict_file:
				spec |= ast.literal_eval(dict_file.read())

		else:
			is_maude_file = True

		# Accumulate source files
		if is_maude_file:
			sources.append(filename)
		else:
			spec_files.append(filename)
			source = spec.get('source')

			# source can be either a single filename or a list
			if isinstance(source, list):
				sources.extend(source)
			elif source:
				sources.append(source)

	# The base dir is that of the first specification file (if any)
	basedir = os.path.dirname(spec_files[0]) if spec_files else '.'

	# Load the files in the input specification
	for source_file in sources:
		# Relative path are referred by default to the directory of the input file
		path_from_base = os.path.join(basedir, source_file)
		source_file = path_from_base if os.path.exists(path_from_base) else source_file

		if not maude.load(source_file):
			return None

	return spec


def to_lean(spec: dict, ofile, verbose=False):
	"""Convert a Maude module to a Lean specification"""

	from . import Maude2Lean
	from .lean import Lean3Writer, Lean4Writer

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

	# Select the generator for Lean 3 or Lean 4
	writerClass = Lean3Writer if spec.get('lean-version', 3) == 3 else Lean4Writer

	trans = Maude2Lean(module, spec, verbose=verbose)
	lean = writerClass(ofile, spec)

	trans.translate(lean)

	return 0


def dump_file(file_ids):
	"""Dump a file shipped with the package"""

	for file_id in file_ids:
		# The schema for the translation options
		if file_id == 'maude2lean.schema.json' or file_id == 'schema':
			with (data_root / 'maude2lean.schema.json').open() as sfile:
				for line in sfile:
					sys.stdout.write(line)

		else:
			print(f'error: unknown resource: {file_id}')
			return 1

	return 0


def load_schema(argparse, parser):
	"""Extend the argument parser with the options in the JSON schema"""

	TYPES = {'string': str, 'boolean': str, 'integer': int, 'object': dict}
	METAVARS = {'string': 'NAME', 'boolean': 'YN', 'integer': 'VALUE'}
	IGNORED = frozenset({'description', 'source'})

	# Load the JSON schema included in the package
	with (data_root / 'maude2lean.schema.json').open() as schema_file:
		schema = json.load(schema_file)

	# Class for handling Boolean options
	class BooleanArg(argparse.Action):
		VALUES = {'yes': True, 'y': True, 'on': True, 'true': True,
		          'no': False, 'n': False, 'off': False, 'false': False}

		def __init__(self, *args, **kwargs):
			super().__init__(*args, **kwargs)

		def __call__(self, parser, nsp, raw_value, option_string=None):
			value = self.VALUES.get(raw_value.lower())
			if value is None:
				raise argparse.ArgumentError(self, f'invalid value: {raw_value} (should be yes/no)')
			setattr(nsp, self.dest, value)

	# Default values
	defaults = {}

	# Define an argument for each option in the schema
	for key, value in schema['properties'].items():
		# Property attributes
		arg_type = value.get('type')
		default_value = value.get('default')
		metavar = METAVARS.get(arg_type)

		if default_value is not None:
			defaults[key] = default_value
		elif arg_type == 'object':
			defaults[key] = {}

		# Some options are handled different, ignored, or too
		# complex to be written on the command line
		if key in IGNORED or arg_type == 'object':
			continue

		# Special options for some arguments
		extra = {}

		if arg_type == 'array':
			arg_type, metavar = value['items']['type'], 'NAMES'
			extra['action'] = 'extend'
			extra['nargs'] = '+'
		elif arg_type == 'boolean':
			extra['action'] = BooleanArg
		elif choices := value.get('enum'):
			extra['choices'] = choices

		# Build the description
		description = value.get('description')

		if default_value is not None:
			printed_name = default_value
			if arg_type == 'boolean':
				printed_name = 'yes' if default_value else 'no'
			elif default_value == []:
				printed_name = 'none'
			description += f' (default: {printed_name})'

		parser.add_argument(f'--{key}',
		                    help=description,
		                    default=argparse.SUPPRESS,
		                    type=TYPES[arg_type],
		                    metavar=metavar,
		                    dest=key,
		                    **extra)

	return defaults, schema['properties'].keys()


def main():
	import argparse

	parser = argparse.ArgumentParser(description='Translate Maude specifications to Lean programs')

	parser.add_argument('source', help='Source files', nargs='+')  # either JSON or Maude, at least one
	parser.add_argument('--verbose', '-v', help='Show additional informative messages', action='store_true')
	parser.add_argument('--no-advise', help='Disable Maude advisory messages', dest='advise', action='store_false')
	parser.add_argument('--dump', help='Dump auxiliary file specified in source to standard output', action='store_true')
	parser.add_argument('-o', help='Output file name')

	# Add translation options in the schema to the parser
	opts_group = parser.add_argument_group('Translation options')
	defaults, keys = load_schema(argparse, opts_group)

	args = parser.parse_args()

	# Dump internal file if requested and finish
	if args.dump:
		return dump_file(args.source)

	maude.init(advise=args.advise)

	# Load the translation options from the specification files
	if (spec := handle_input_files(defaults, args.source)) is None:
		return 1

	# The command-line parameters take precedence over the files
	spec |= args.__dict__

	# Take output file name from the command line
	output_file = open(args.o, 'w') if args.o else sys.stdout

	return to_lean(spec, output_file, args.verbose)


if __name__ == '__main__':
	sys.exit(main())
