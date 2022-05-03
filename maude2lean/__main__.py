#
# Entry point of the Maude to Lean translator
#

import sys
import maude


def handle_input_file(filename: str):
	"""Handle the input file"""

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
	else:
		spec = {'source': filename}

	# Load the files in the input specification
	# (either a single one or a list of them)
	source_files = spec.get('source')

	if source_files:
		source_files = source_files if isinstance(source_files, list) else (source_files,)

		for source_file in source_files:
			maude.load(source_file)

	return spec


def to_lean(module_name: str, spec: dict, ofile):
	"""Convert a Maude module to a Lean specification"""

	from . import Maude2Lean
	from .lean import LeanWriter

	module = maude.getModule(module_name) if module_name else maude.getCurrentModule()

	trans = Maude2Lean(module, spec)
	lean = LeanWriter(ofile, spec)

	trans.translate(lean)


def main():
	import argparse

	parser = argparse.ArgumentParser(description='Universal checker for Maude modules')

	parser.add_argument('source', help='Source file')
	parser.add_argument('module', help='Module', nargs='?')
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

	return to_lean(module, spec, output_file)


if __name__ == '__main__':
	sys.exit(main())
