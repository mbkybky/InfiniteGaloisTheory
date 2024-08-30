# Lean blueprints

## Installation

This package depends on `plastexdepgraph` which requires graphviz and its development libraries. 
If you have a user-friendly OS, it is as simple as 
`sudo apt install graphviz libgraphviz-dev`. 
See https://pygraphviz.github.io/documentation/stable/install.html otherwise.

Then, assuming you have a sane python environment, you only need to run:
```
pip install leanblueprint
```
Note this will automatically install plasTeX and the other needed python
packages.

## Local compilation

Assuming you used the `leanblueprint` command line tool to create your blueprint
(or at least that you use the same file layout), you can use `leanblueprint` to
build your blueprint locally. The available commands are:

* `leanblueprint pdf` to build the pdf version (this requires a TeX installation
  of course).
* `leanblueprint web` to build the web version
* `leanblueprint checkdecls` to check that every Lean declaration name that appear
  in the blueprint exist in the project (or in a dependency of the project such
  as Mathlib). This requires a compiled Lean project, so make sure to run `lake build` beforehand.
* `leanblueprint all` to run the previous three commands.
* `leanblueprint serve` to start a local webserver showing your local blueprint
  (this sounds silly but web browsers paranoia makes it impossible to simply
  open the generated html pages without serving them). The url you should use
  in your browser will be displayed and will probably be `http://0.0.0.0:8000/`,
  unless the port 8000 is already in use.

Note: plasTeX does not call BibTeX. If you have a bibliography, you should use
`leanblueprint pdf` before `leanblueprint web` to get it to work in the web
version (and redo it when you add a reference).

## Editing the blueprint

Assuming you used the `leanblueprint` command line tool to create your blueprint
(or at least that you use the same file layout), the source of your blueprint
will be in the `blueprint/src` subfolder of your Lean project folder.

Here you will find two main TeX files: `web.tex` and `print.tex`. The first one
is intended for plasTeX while the second one is intended for a traditional TeX
compiler such as `xelatex` or `lualatex`. 
Each of them includes `macros/common.tex` for all TeX macros that make sense
for both kinds of outputs (this should be most of your macros). 
Macros that should behave differently depending on the target format should go
to either `macros/web.tex` or `macros/print.tex`. All those files already exist
and contains comments reminding you about the above explanations.

The main content of your blueprint should live in `content.tex` (or in files
imported in `content.tex` if you want to split your content).

The main TeX macros that relate your TeX code to your Lean code are:

* `\lean` that lists the Lean declaration names corresponding to the surrounding
  definition or statement (including namespaces).
* `\leanok` which claims the surrounding environment is fully formalized. Here
  an environment could be either a definition/statement or a proof.
* `\uses` that lists LaTeX labels that are used in the surrounding environment.
  This information is used to create the dependency graph. Here
  an environment could be either a definition/statement or a proof, depending on
  whether the referenced labels are necessary to state the definition/theorem
  or only in the proof.

For more information of lean blueprint, please visit : https://github.com/PatrickMassot/leanblueprint