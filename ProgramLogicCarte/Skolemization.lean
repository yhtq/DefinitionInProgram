import ProgramLogicCarte.Wpi
import ProgramLogicCarte.WpiStructural

/-! Structural rules for interaction-tree weakest preconditions. -/
namespace Skolemization

open Iris Iris.BI Iris.OFE ITree ProgramLogicCarte


variable {GF : BundledGFunctors}
    [InvGS_gen hlc GF]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandler GF ε)
    (t : ITree ε ρ) {α : Type*} (A : α -> ρ → IProp GF)
    {P : IProp GF}
    (source : ⊢ {{{ P }}} t @@ H {{{fun r => ∃ a, A a r}}})

#synth BI (IProp GF)
#check UPred.instBIUPred


theorem skolemization_conservative
    {Q : IProp GF}
    (hQ : ∀ a, ({{{ P }}} t @@ H {{{A a}}}) ⊢ Q) :
    ⊢ Q := by
  iintro Htriple
