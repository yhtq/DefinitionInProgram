import IrisTutorial.Programs

/-! Exercise skeleton for tutorial unit 1. Replace `sorry` with a proof. -/

namespace IrisTutorial.Exercises.Ex01Swap

open Iris BI ProgramLogic
open Iris.HeapLang
open IrisTutorial

theorem rotateLeft_spec {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]
    (x y z : Loc) (v1 v2 v3 : Val) :
    {{ x ↦ some v1 ∗ y ↦ some v2 ∗ z ↦ some v3 }} hl(&rotateLeft #x #y #z)
    {{ RET hl_val(#()); x ↦ some v2 ∗ y ↦ some v3 ∗ z ↦ some v1 }} := by
  sorry

end IrisTutorial.Exercises.Ex01Swap
