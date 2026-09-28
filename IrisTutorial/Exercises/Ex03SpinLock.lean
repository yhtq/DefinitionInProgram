import IrisTutorial.Solutions.Ex03SpinLock

/-! Exercise 3 entry point. Prove the exported `try_acquire_spec`,
`acquire_spec`, and `release_spec` from the SpinLock implementation. -/

namespace IrisTutorial.Exercises.Ex03SpinLock

open Iris BI ProgramLogic
open Iris.HeapLang

theorem exercise_marker : True := by
  trivial

end IrisTutorial.Exercises.Ex03SpinLock
