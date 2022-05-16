Verification of KeYmaeraX's core in Coq
=======================================


This repository contains a formalization of KeYmaeraX's core in Coq.
It includes a formalization of the syntax, dynamic semantics, and
static semantics of Differential dynamic logic (dL), as well as a
formalization of Uniform Substitution.  We have implemented (and
verified the validity of) dL's Differential Dynamic Logic and ODE
axioms.  We have also implemented a proof checker to write and check
dL proofs in Coq.  Here are some useful links regarding this
formalization:

* We described our formalization in the following paper:
  [Formally verified differential dynamic logic](http://dx.doi.org/10.1145/3018610.3018616),
  Rose Bohrer,
  [Vincent Rahli](http://www.cs.bham.ac.uk/~rahliv/),
  [Ivana Vukotic](http://wwwen.uni.lu/snt/people/ivana_vukotic),
  [Marcus Völp](http://wwwen.uni.lu/snt/people/marcus_voelp)
  and [André Platzer](http://symbolaris.com),
  [CPP 2017](http://cpp2017.mpi-sws.org).

* The above paper covers both our Coq formalization and
  Rose's
  [Isabelle/HOL formalization](https://github.com/LS-Lab/Isabelle-dL).

* KeYmaeraX sourcecode is available
[here](https://github.com/LS-Lab/KeYmaeraX-release).

* The technical report about uniform substitution is available
[here](http://arxiv.org/pdf/1601.06183.pdf).


Contributors
------------

* [Vincent Rahli](http://www.cs.bham.ac.uk/~rahliv/)
* [Ivana Vukotic](http://wwwen.uni.lu/snt/people/ivana_vukotic)
* [Marcus Völp](http://wwwen.uni.lu/snt/people/marcus_voelp)

If you have any question, please send an email to
[Vincent](http://www.cs.bham.ac.uk/~rahliv/).

This work was supported by the SnT and the National Research Fund
Luxembourg (FNR), through PEARL grant FNR/P14/8149128.


Install and Dependencies
------------------------


* Our formalization compiles with Coq 8.9.1, which you can get through
opam.  [Here](https://opam.ocaml.org/doc/Usage.html)'s how to get
started with opam.  We're using opam version 2.0.3 and we're using
OCaml version 4.05.0.  You might have to switch the OCaml version in
opam, using `opam switch`.  To get Coq through opam, simply type:

    `opam install coq`

* We're editing files using the ProofGeneral Emacs interface for Coq.
You can find ProofGeneral and instructions on how to install it
[here](https://proofgeneral.github.io/).

* We are using version 3.0.2 of the
[coquelicot](http://coquelicot.saclay.inria.fr/) library for real
analysis, which you can get through opam:

   `opam install coq-coquelicot`

Coquelicot depends on ssreflect.  Installing coquelicot through opam
should install ssreflect as well.  If for some reason you want to
install it manually, simply type:

    `opam install coq-mathcomp-ssreflect`.

* To compile all files you can evaluate in all.v using ProofGeneral,
which is going to compile our examples and their dependencies.
Alternatively, you can run:

    `./create_makefile.sh`

    to generate a Makefile; followed by:

    `make -j n`

    (where n is the number of cores you want to use to compile the
project).  Make sure that you've pulled the submodules before you run
`./create_makefile.sh`, otherwise the dependencies won't be computed
right.

* If you want to use ProofGeneral, and you're not sure what to do,
here's what you can try to do: open all.v using Emacs. If you've
installed ProofGeneral as instructed above, the ProofGeneral logo
should appear when you start Emacs. If not, something went wrong. If
the logo does show up in your Emacs buffer, then go to the end of the
file and hit C-c C-RET. Assuming that the `coq-compile-before-require`
variable is set to true, it should compile the file and all its
dependencies.

* If you want to try to prove something yourself, look for example
at examples/example1.v.


Roadmap
-------


This repository is organized into the following folders:

1. coq-tools: a submodule containing some useful tactics
2. syntax: syntax of Terms, Formulas, Hybrid Programs and ODEs
3. semantics: static semantic, dynamic semantics as well as
     soundness of static semantics (coincidence lemmas)
4. substitution: uniform substitution and its
     correctness, as well as uniform and bound
     variable renaming
5. axioms: DDL and ODE axioms
6. checker: sequent calculus and proof checker
6. examples: examples of proofs that use our proof checker
