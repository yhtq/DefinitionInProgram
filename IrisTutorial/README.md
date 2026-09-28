# POPL'21 Iris tutorial — Iris-Lean port

This directory ports the five programs from the [POPL'21 Iris tutorial][src]
to the `iris-lean` API used by this repository.  It keeps exercise entry
points separate from reference-solution entry points.

| Original unit | Lean exercise | Lean solution |
| --- | --- | --- |
| `ex_01_swap.v` | `Exercises/Ex01Swap.lean` | `Solutions/Ex01Swap.lean` |
| `ex_02_sumlist.v` | `Exercises/Ex02SumList.lean` | `Solutions/Ex02SumList.lean` |
| `ex_03_spinlock.v` | `Exercises/Ex03SpinLock.lean` | `Solutions/Ex03SpinLock.lean` |
| `ex_04_parallel_add.v` | `Exercises/Ex04ParallelAdd.lean` | `Solutions/Ex04ParallelAdd.lean` |
| `ex_05_parallel_add_mul.v` | `Exercises/Ex05ParallelAddMul.lean` | `Solutions/Ex05ParallelAddMul.lean` |

`Programs.lean` contains the shared direct HeapLang translations.  Unit 2's
linked-list predicate is in `Exercise02List.lean`.  Unit 3 reuses the
machine-checked `Iris.HeapLang.SpinLock` implementation, whose API is a
slightly stronger version of the tutorial API: ownership after acquire is
`locked γ ∗ R`, and release consumes that token.

The first solution (`swap_spec`) is fully checked.  The remaining exercise
holes and longer solution proofs are intentionally marked `sorry`, so their
statements and all embedded programs typecheck while retaining explicit proof
targets.  This is necessary because their Coq proof scripts rely on tactics
(`iInduction`, Coq resource-algebra automation) for which this version of
`iris-lean` has no mechanical one-to-one translation.

Build with the repository's Nix-provided toolchain:

```sh
nix develop --command lake build IrisTutorial
```

[src]: https://gitlab.mpi-sws.org/iris/tutorial-popl21/-/tree/master
