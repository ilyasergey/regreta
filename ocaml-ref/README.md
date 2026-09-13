# OCaml reference driver

This directory builds a thin command-line driver on top of the algorithm modules of the
[Greta](https://github.com/verse-lab/greta) reference implementation, so that the OCaml
code and the Lean formalisation can be run on the same inputs and compared.

The Greta sources are *not* vendored here.  `./fetch.sh` clones the upstream repository at
a pinned commit into `.greta/` and copies the modules the driver needs into `src/`.  Both
directories are ignored by git.

    ./fetch.sh          # clone upstream and stage the sources
    dune build          # build ./_build/default/driver/main.exe

The driver speaks the same text format as `lake exe greta`; see `../docs/testing.md` for
the format and `../docs/reproducing.md` for the comparison procedure.

Upstream is MIT licensed, Copyright (c) 2022 Yunjeong Lee.
