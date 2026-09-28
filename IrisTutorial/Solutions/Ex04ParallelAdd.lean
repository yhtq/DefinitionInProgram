import IrisTutorial.Programs
import Iris.HeapLang.Lib.Par

/-! Reference proof target for tutorial unit 4 (parallel addition).

The two original ghost-state variants map to Iris-Lean's authoritative resource
algebras; this statement preserves the tutorial's final, exact-result goal. -/

namespace IrisTutorial.Solutions.Ex04ParallelAdd

open Iris BI ProgramLogic
open Iris.HeapLang
open IrisTutorial

theorem parallelAdd_spec {hlc} {GF : BundledGFunctors}
    [HeapLangGS hlc GF] [Spawn.SpawnG GF] :
    {{ (True : IProp GF) }} hl(&parallelAdd)
    {{ RET hl_val(#(4 : Int)); (True : IProp GF) }} := by
  sorry

end IrisTutorial.Solutions.Ex04ParallelAdd
