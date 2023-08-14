#
# Makefile for the maude2lean tool
#

# Python command to be included in the shebang
PYTHON ?= /usr/bin/env python3

# Bundle the all the Python and data file into single executable zip file
# (based on Stack Overflow's question 17486578)

RESOURCES = maude2lean/data/*.lean maude2lean/data/*.lean4 maude2lean/data/*.json
CODE      = maude2lean/*.py

dist/maude2lean: dist $(RESOURCES) $(CODE)
	# Create temporary directory and copy the package into it
	mkdir -p zip
	cp -r maude2lean zip
	# Create a __main__ file for the package that invokes the maude2lean one
	echo -e 'import sys\nfrom maude2lean.__main__ import main\nsys.exit(main())' > zip/__main__.py
	touch -ma zip/* zip/*/*
	# Compress that directory into a zip file
	cd zip ; zip -q ../maude2lean.zip $(RESOURCES) $(CODE) __main__.py
	rm -rf zip
	# Put the shebang and then the zip file into the executable bundle
	echo '#!$(PYTHON)' > dist/maude2lean
	cat maude2lean.zip >> dist/maude2lean
	rm maude2lean.zip
	chmod a+x dist/maude2lean

wheel:
	pip wheel --no-deps -w dist .

dist:
	mkdir -p dist
