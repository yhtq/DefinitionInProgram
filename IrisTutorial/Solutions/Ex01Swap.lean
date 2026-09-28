import IrisTutorial.Programs

/-! Solutions for exercise 1: swapping and rotating heap locations. -/

namespace IrisTutorial.Solutions.Ex01Swap

open Iris BI ProgramLogic
open Iris.HeapLang
open IrisTutorial

theorem swap_spec {hlc} {GF : BundledGFunctors}
    [HeapLangGS hlc GF] (x y : Loc) (v1 v2 : Val) :
    {{ x ↦ some v1 ∗ y ↦ some v2 }} hl(&swap #x #y)
    {{ RET hl_val(#()); x ↦ some v2 ∗ y ↦ some v1 }} := by
  iintro %Φ ⟨Hx, Hy⟩ Hcont
  unfold swap
  wp_rec
  wp_load
  wp_load
  wp_store
  wp_store
  iapply Hcont
  iframe

end IrisTutorial.Solutions.Ex01Swap
