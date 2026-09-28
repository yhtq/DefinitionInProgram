import ProgramLogicCarte.SIProp
import ProgramLogicCarte.WpiStructural

/-! Structural rules for interaction-tree weakest preconditions. -/
namespace Skolemization

open Iris Iris.BI Iris.OFE ITree ProgramLogicCarte


variable {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (t : ITree ε ρ) {α : Type*} (A : α -> ρ → PROP)
    {P : PROP}
    (source : ⊢ {{{ P }}} t @@ H {{{fun r => ∃ a, A a r}}})

#synth BI (PROP)
#check UPred.instBIUPred


theorem skolemization_conservative
    {Q : PROP}
    (hQ : ∀ a, ({{{ P }}} t @@ H {{{A a}}}) ⊢ Q) :
    ⊢ Q := by
  iintro Htriple
