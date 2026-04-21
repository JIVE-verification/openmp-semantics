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

Files are under [omp_compiler](omp_compiler).

- [roadmap.md](omp_compiler/roadmap.md) has some notes about the compiler passes.
- [ClightT.md](omp_compiler/ClightT.md) defines programT, a lifted Clight program
  that can include pragma_info, analysis information about `Spragma`s.
- [src1.c](omp_compiler/sample/src1.c) is a sample input to the compiler.
  [src1_tweak.v](omp_compiler/sample/src1_tweak.v) is the corresponding AST.
  The spragma and pragma_info part are added manually for now.
  [tgt1.c](omp_compiler/sample/tgt1.c) and [tgt1.v](/omp_compiler/sample/tgt1.v)
  are what the compiler's output is supposed to look like for
  [src1.c](omp_compiler/sample/src1.c).
- [O2Clight.v](omp_compiler/O2Clight.v) has the compiler passes.

## Building

[Install opam](https://opam.ocaml.org/doc/Install.html), then create an opam switch:

```(bash)
opam switch create ClightOMP ocaml-variants.4.14.1+options ocaml-option-flambda
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
make omp # compiles files registered in Makefile
```

Alternatively,
```(bash)
make PATH_TO_FILE (with .v replaced by .vo)
```
e.g.
```
make concurrency/openmp_sem/HybridMachine.vo
make omp_compiler/O2Clight.vo
```

Additionally, generate `_CoqProject` if your Rocq IDE needs it:

```(bash)
make _CoqProject
```

## Misc

- After making changes to file names or creating a new .v file, edit
  make the corresponding changes to `OMP_COMPILER_FILES` in [Makefile](Makefile),
  and update the dependency file `.depend` and `_CoqProject` by
  ```
  make .depend -B
  make _CoqProject -B
  ```
  
- Some convenient commands to compile/clean the `omp_compiler` folder:
  ```(bash)
  make omp
  make clean-omp
  ```