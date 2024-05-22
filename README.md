# simp_lang

[![CI](https://github.com/tchajed/iris-simp-lang/actions/workflows/build.yml/badge.svg)](https://github.com/tchajed/iris-simp-lang/actions/workflows/build.yml)

simp_lang is a very simple programming language that we instantiate Iris with.
On top of that Iris gives a program logic based on weakest preconditions. It is
heavily inspired by heap_lang (and mostly copied from it) but aims to simplify
things down as much as possible while still supporting verifying concurrent
programs.

You might want to start with a [high-level conceptual
overview](https://youtu.be/HndwyM04KEU) (links to a YouTube video; if you'd
prefer there's a [static version](tutorial/)):

[![](tutorial/slides/simp_lang.019.png)](https://youtu.be/HndwyM04KEU)

This overview might be useful before diving into this code, which works out all
the details and goes a step beyond by also doing some program verification in our
new language.

The recommended reading order for this tutorial is the following:

1. [lang.v](src/lang.v) defines the syntax and semantics of simp_lang (instantiating `ectxi_language`)
2. [primitive_laws.v](src/primitive_laws.v) defines a _state interpretation_
   for simp_lang (instantiating
   `irisG simp_lang`). This is the connection between the state of simp_lang (a
   heap from locations to values) and the Iris logic.
3. [heap_ra.v](src/heap_ra.v) and [heap_lib.v](src/heap_lib.v) are the mechanism for the state interpretation,
   which will make more sense after seeing them used.
4. [adequacy.v](src/adequacy.v) sets up the generic language adequacy theorem
   with an initialization of the state interpretation for simp_lang.

Next, you can check out some examples from the [Iris POPL 2021 tutorial](https://gitlab.mpi-sws.org/iris/tutorial-popl21/) that are
re-implemented and verified in simp_lang:

1. [examples/swap.v](src/examples/swap.v) verifies a version of swap.
2. [examples/parallel_add.v](src/examples/parallel_add.v) verifies the parallel
   increment example. It also demonstrates applying the adequacy theorem to
   derive a theorem about `parallel_add` whose statement is independent of Iris.

There are a few files that are optional reading which make the tutorial work:

- [tactics.v](src/tactics.v) and
  [class_instances.v](src/class_instances.v) are necessary parts of the
  implementation but aren't directly related to instantiating Iris.
- [notation.v](src/notation.v) makes it possible to write programs in simp_lang
- [proofmode.v](src/proofmode.v) gives enough proofmode support to actually
  verify programs written in simp_lang.
- [examples/spawn.v](src/examples/spawn.v) and
  [examples/par.v](src/examples/par.v) implement and verify the par combinator
  (`e1 ||| e2`) used in the tutorial example.

## Compiling

This development relies on a development version of Iris and Coq 8.18 or later.
We test 8.18, 8.19, and master with Iris dev in CI, as well as the released
version of Iris.

You'll need to install Iris, which is easiest done through opam. There are
installation instructions at https://gitlab.mpi-sws.org/iris/iris.
