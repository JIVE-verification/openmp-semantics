# Goal
Write a compiler from concurrent C + omp pragmas (ClightOMP) to concurrent C (CPM), and verify correctness.

## Compiler
The target lang is Clight + concurrent primitives (spawn + lock functions).
Source lang: should probably be Clight, otherwise compiler correctness theorem might be tricky. Two issues:

1. [compcert frontend](https://compcert.org/doc/) has these passes: `CompCert C =SimplExpr=> Clight_1 =[simplLocals]=> Clight_2`,
where `Clight_1,2` are both Clight but the simplLocals pass does the stack allocation optimization, which we don't want (because compcert frontend ignores pragmas and therefore don't know anything about shared variables in OpenMP context), so we do `clightgen -csyntax` to generate CompCert C, then manually apply the SimplExpr pass, then add the OpenMP annotations.
2. To write the passes, we need information about the (shared, private, reduction, local) variables. However compcert hoists local variable definitions (because there are no "block" in Clight), so at least information about local vars is lost in Clight. We assume this analysis info is given for now.

### parallel pragma
Types of different variables and their treatments when making a thread routine (e.g. translating the parallel region in [cmplr_src1.c](./cmplr_src1.c) to [complr_tgt1.c:_par_routine1](./cmplr_tgt1.c)):

1. privatized variable, must be shared in the outer parallel region. A declaration of the same type and ident shall be copied to the routine (TODO can the idents be the same? there would be two variables).
2. reduction variable, similar to 1, and address of the original copy shall be passed to the routine, and contributions shall be added to the original copy. One easy way is for the working thread to do this right before it terminates.
3. local, declared in this parallel region. There is no usage of a local variable before this parallel region, and it should be safe to move/copy the definition to the thread routine.  
4. otherwise, is declared outside of this parallel region and not in private or reduction clause, thus shared. The address of this shared variable (say, `a`) shall be passed as argument to the routine, and all accesses shall be changed to use the address (`a` => `*a_ptr`).

The thread that meets `pragma omp parallel num_threads(n)` should spawn `n-1` threads with the rountine, then run the routine, then join spawned threads.

### for pragma
compute a partition of the loop iteration (this needs to be done at compile time because boundaries can be decided by runtime variables... this sounds annoying to verify).

### critical
Each critical pragma can just be translated to a pair of lock acquire/release

### others
Locks used in critical sections and reductions shall be initialized at the beginning of main() and destroyed at end of main().