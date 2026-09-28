import Iris.HeapLang.Lib.SpinLock

/-! Unit 3 is provided by Iris-Lean's verified spin-lock library.
The original tutorial's `R`-only lock ownership is refined here with an
exclusive `locked γ` token, which is required to make release sound. -/

namespace IrisTutorial.Solutions.Ex03SpinLock

open Iris BI ProgramLogic
open Iris.HeapLang

export Iris.HeapLang.SpinLock (newlock tryAcquire acquire release isLock locked
  newlock_spec try_acquire_spec acquire_spec release_spec)

end IrisTutorial.Solutions.Ex03SpinLock
