import setuptools

long_description = '''# A Maude to Lean translator

Translate a Maude module to a Lean specification where terms, sort membership,
equational, and rewriting relations are inductively defined.
'''

setuptools.setup(
	name                          = 'maude2lean',
	version                       = '0.1',
	author                        = 'ningit',
	author_email                  = 'ningit@users.noreply.github.com',
	description                   = 'Maude to Lean translator',
	long_description              = long_description,
	long_description_content_type = 'text/markdown',
	url                           = 'https://github.com/fadoss/maude2lean',
	project_urls                  = {
		'Bug Tracker'   : 'https://github.com/fadoss/maude2lean/issues',
		'Documentation' : 'https://github.com/fadoss/maude2lean',
		'Source Code'   : 'https://github.com/fadoss/maude2lean'
	},
	license                       = 'GPLv3',
	packages                      = setuptools.find_packages(),
	package_data                  = {'': ['data/*']},
	include_package_data          = True,
	entry_points                  = {
		'console_scripts': [
			'maude2lean=maude2lean.__main__:main'
		]
	},
	classifiers                   = [
		'Programming Language :: Python :: 3',
		'Intended Audience :: Science/Research',
		'License :: OSI Approved :: GNU General Public License v3 (GPLv3)',
		'Topic :: Scientific/Engineering',
		'Operating System :: OS Independent',
	],
	python_requires               = '>=3.9',
	install_requires              = [
		'maude >= 1.1.1',
	]
)
