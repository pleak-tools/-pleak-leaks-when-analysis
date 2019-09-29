
# The implementation of the SQL and BPMN leaks-when analysis tools for pleak.io.

## Requirements

For both analysis tools:

- Z3 Theorem Prover - to install, you can clone it from [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3) and compile it yourself or (on some Linux versions, for example Ubuntu) execute `apt install z3`. You will need Z3 to be in the PATH.
- opam (`apt install opam`)
- ocaml (`apt install ocaml`) - version 4.02.0 is needed (`opam switch 4.02.0`)
- ocamlgraph (`opam install ocamlgraph` / `apt install libocamlgraph-ocaml-dev`)
- xml-light (`opam install xml-light` / `apt install libxml-light-ocaml-dev`)
- Yojson (`opam install Yojson`)

Based on environment, you might also need to install:

- m4 (`apt install m4`)
- ocamlfind (`opam install ocamlfind`)

## Installing & building

For the SQL leaks-when analysis tool:

Read Installing & building instructions in [pleak-leaks-when-ast-transformation](https://github.com/pleak-tools/pleak-leaks-when-ast-transformation) repository.

For the BPMN leaks-when analysis tool:

Execute `ocamlbuild -use-ocamlfind GrbDriver.native` in \src directory.

## Using

You can use both analysers through [Pleak SQL-privacy editor](https://github.com/pleak-tools/pleak-sql-editor).

## License

MIT