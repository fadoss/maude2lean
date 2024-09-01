Maude to Lean translator
========================

Translate [Maude](https://maude.cs.illinois.edu) modules to [Lean](https://leanprover.github.io/) specifications where terms, sort membership, equational, and rewriting relations are defined inductively. Hence, theorems about Maude specifications can be proven in Lean.

The syntax of the tool is
```
$ maude2lean <Maude source or JSON/YAML/TOML file>+ [-o <output file>]
```
where the arguments are either a Maude file or a JSON, YAML, or TOML specification to customize the translation. The available options are documented in this [JSON schema](maude2lean.schema.json), and most of them can also be passed as command-line options (use `--help` for a list). Examples are available in the [test](test) directory.

The installation requirements for `maude2lean` are Python 3.9 and the [maude](https://pypi.org/project/maude) Python library. Wheels and bundles are available in the [releases](https://github.com/fadoss/maude2lean/releases/tag/latest) section of this repository.

For a detailed description of the translation, see [*Maude2Lean: Theorem proving for Maude specifications using Lean*](https://doi.org/10.1016/j.jlamp.2024.101005) or its shorter [conference version](https://doi.org/10.1007/978-3-031-17244-1_16).
