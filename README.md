# A Formal Semantics of C with OpenMP Parallelism

The repository contains a formalization of the OpenMP semantics on top of the 
Clight semantics.
The work is adapted from the [CPM](https://www.cs.princeton.edu/techreports/2020/002.pdf) semantics,
and the mechanization builds on a fork of [VST](https://github.com/PrincetonUniversity/VST).
We omit irrelevant files from the VST repository.

## Files

### Semantics

- [concurrency/openmp_sem/HybridMachine.v](concurrency/openmp_sem/HybridMachine.v)
  formalizes the ClightOMP semantics. In particular, `pragma_step` is the small-step
  operational semantic rules for OpenMP pragmas;
   `ext-step` is the rules for lock steps (from CPM);
  Clight rules ("`dry_step`") are mostly unchanged.
  `Ostep` is the top-level rule that includes the above.
- [concurrency/openmp_sem/team_dyn.v](concurrency/openmp_sem/team_dyn.v)
  defines the team tree and its operations.
- [concurrency/openmp_sem/reduction.v](concurrency/openmp_sem/reduction.v)
  defines privatization and reduction operations.
- [compcert/cfrontend/Clight.v](compcert/cfrontend/Clight.v)
  extends Clight syntax to support OpenMP pragmas.
- [concurrency/openmp_sem/parallel_for_omp_exec.v](concurrency/openmp_sem/parallel_for_omp_exec.v)
  an example of executing some OpenMP program 
  [concurrency/openmp_sem/parallel_for.c](concurrency/openmp_sem/parallel_for.c).
  The OpenMP pragma part of its AST ([concurrency/openmp_sem/parallel_for.v](concurrency/openmp_sem/parallel_for.v)) is added manually for now.
  
### Compiler

TODO fill this in

## Building

[Install opam](https://opam.ocaml.org/doc/Install.html), then create an opam switch:

```(bash)
opam switch create vst_on_iris ocaml-variants.4.14.1+options ocaml-option-flambda
```

Install dependencies:

```(bash)
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add builddep/
```

Download submodules:
```(bash)
git submodule update --init --recursive
```

Now we can use [`Makefile`](./Makefile) to compile the Rocq files:

```(bash)
make concurrency/openmp_sem/HybridMachine.vo
```

Additionally, to generate `_CoqProject`:

```(bash)
make _CoqProject