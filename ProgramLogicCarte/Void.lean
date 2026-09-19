import ProgramLogicCarte.Handler
import ITree.Translate

/-! The empty effect and its logical handler (`src/void.v`). -/

namespace ProgramLogicCarte

open Iris Iris.BI ITree

universe u v uₑ

/-- The empty logical handler; there is no event to interpret. -/
def voidH {GF : BundledGFunctors} : IHandler GF (VoidE : Type u → Type v) where
  handle e := nomatch e
  mono e := nomatch e
  ne e := nomatch e

instance voidHSequential {GF : BundledGFunctors} :
    IHandler.Sequential (voidH : IHandler GF (VoidE : Type u → Type v)) where
  sequential e := nomatch e

/-- Embed a tree into the coproduct with the empty effect. -/
def insertVoid {ε : Type u → Type v} {ρ : Type uₑ} (t : ITree ε ρ) :
    ITree (ε + VoidE) ρ :=
  translate (fun e => SumE.inl e) t

@[simp]
theorem insertVoid_ret {ε : Type u → Type v} {ρ : Type uₑ} (x : ρ) :
    insertVoid (ε := ε) (ret x) = ret x :=
  translate_ret _ _

@[simp]
theorem insertVoid_tau {ε : Type u → Type v} {ρ : Type uₑ} (t : ITree ε ρ) :
    insertVoid (tau t) = tau (insertVoid t) :=
  translate_tau _ _

@[simp]
theorem insertVoid_vis {ε : Type u → Type v} {ρ : Type uₑ} {α : Type u}
    (e : ε α) (k : α → ITree ε ρ) :
    insertVoid (vis e k) = vis (SumE.inl e) (fun x => insertVoid (k x)) :=
  translate_vis _ _ _

end ProgramLogicCarte
