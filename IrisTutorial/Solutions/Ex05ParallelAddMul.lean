import IrisTutorial.Programs
import Iris.HeapLang.Lib.Par
import Iris.HeapLang.Lib.SpinLock

/-! Reference proof target for tutorial unit 5 (locked parallel add/multiply). -/

namespace IrisTutorial.Solutions.Ex05ParallelAddMul

open Iris BI ProgramLogic
open Iris.HeapLang
open IrisTutorial

theorem parallelAddMul_spec {hlc} {GF : BundledGFunctors}
    [HeapLangGS hlc GF] [Spawn.SpawnG GF] [SpinLock.SpinLockG GF] :
    {{ (True : IProp GF) }} hl(&parallelAddMul)
    {{ (z : Int), RET hl_val(#z); ⌜z = 2 ∨ z = 4⌝ }} := by
  sorry

end IrisTutorial.Solutions.Ex05ParallelAddMul
