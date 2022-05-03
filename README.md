Maude to Lean translator
========================

Translate [Maude](https://maude.cs.illinois.edu) modules to [Lean](https://leanprover.github.io/) 3 specifications where terms, sort membership, equational, and rewriting relations are defined inductively. Hence, theorems about Maude specifications can be proven in Lean.

The syntax of the tool is
```
$ maude2lean <Maude source or JSON/YAML file> [<module name>] [-o <output file>]
```
where the first argument is the path of either a Maude file or a JSON or YAML specification to customize the translation. The available options are documented in this [JSON schema](maude2lean.schema.json). Examples are available in the [test](test) directory.

The installation requirements for `maude2lean` are Python 3.9 and the [maude](https://pypi.org/project/maude) Python library. Wheels and bundles are available in the [releases](https://github.com/fadoss/maude2lean/releases/tag/latest) section of this repository.