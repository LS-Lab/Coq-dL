Verification of KeYmaeraX's core in Coq
=======================================


This repository contains a formalization of KeYmaeraX's core in Coq.
It includes a formalization of the syntax, dynamic semantics, and
static semantics of Differential dynamic logic (dL), as well as a
formalization of Uniform Substitution.  We have implemented (and
verified the validity of) dL's Differential Dynamic Logic and ODE
axioms.  We have also implemented a proof checker to write and check
dL proofs in Coq.


KeYmaeraX sourcecode is available
[here](https://github.com/LS-Lab/KeYmaeraX-release).

The technical report about uniform substitution is available
[here](http://arxiv.org/pdf/1601.06183.pdf).


Contributors
------------

* [Vincent Rahli](http://wwwen.uni.lu/snt/people/vincent_rahli)
* [Marcus Völp](http://wwwen.uni.lu/snt/people/marcus_voelp)
* [Ivana Vukotic](http://wwwen.uni.lu/snt/people/ivana_vukotic)

If you have any question, please send an email to either of us
(preferably Vincent).  You can find our email addresses on the [CritiX
webpage](http://wwwen.uni.lu/snt/research/critix/).

This work is supported by the SnT and the National Research Fund
Luxembourg (FNR), through PEARL grant FNR/P14/8149128.


Install and Dependencies
------------------------


* Our formalization compiles with Coq 8.5pl2 (I've been told it works
with 8.5pl1 too), which you can get through opam.
[Here](https://opam.ocaml.org/doc/Usage.html)'s how to get started
with opam.  We're using opam version 1.2.2 and we're using OCaml
version 4.03.0.  You might have to switch the OCaml version in opam,
using `opam switch`.  To get Coq through opam, you have to add the
following repository:

    `opam repo add coq-released https://coq.inria.fr/opam/released`

    after that you can run:

    `opam install coq`

* We're editing files using the ProofGeneral Emacs interface for Coq.
You can find ProofGeneral and instructions on how to install it
[here](https://github.com/ProofGeneral/PG).

* Here's what I've got regarding ProofGeneral in my .emacs.el file:

   `(load "~/.emacs.d/lisp/PG/generic/proof-site")`

   `(setq coq-compile-before-require t)`

* We are using version 2.1.1 of the
[coquelicot](http://coquelicot.saclay.inria.fr/) library for real
analysis.  There is a .tag.gz archive in this repository (they don't
seem to have a git repository).  Just untar it to start using it.  It
requires ssreflect (we're using version 1.6).  The best way to get
ssreflect is through opam by running:

    `opam install coq-mathcomp-ssreflect.1.6`

* This branch also uses [CoRN](http://corn.cs.ru.nl/).  To install
CoRN through opam, run:

    `opam install coq-corn`

* If you've cloned this repository, you'll need to pull the submodules
by running:

    `git submodule init`

    followed by:

    `git submodule update`.

    Otherwise, if it's an archive you've got, they should be part of the
archive (only the coq-tools directory for the archive).

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
here's what you can try to do: open all.v using Emacs.  If you've
installed ProofGeneral as instructed above, the ProofGeneral logo
should appear when you start Emacs.  If not, something went wrong.  If
the logo does show up in your Emacs buffer, then go to the end of the
file and hit C-c C-RET.  Assuming that you set the
`coq-compile-before-require` variable to true, it should compile the
file and all its dependencies.

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
