import ProgramLogicCarte.State
import ProgramLogicCarte.WpiStructural

/-! Relational adequacy for stateful interaction trees.

`StateIrel` includes returns, silent steps, external events and state operations.
The main theorem accepts any related target tree; `stateIfn` is a corollary. -/

namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE ITree

universe u uρ w

/-- Induction invariant transferring source WP to a related interpreted tree.
The quantifier over all targets is essential for the coinductive relation. -/
def stateAdequacyPred {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {ε : Type u → Type u} {ρ : Type uρ}
    (H : IHandlerBase PROP ε) (source : WpiState PROP (StateE S + ε) ρ) : PROP :=
  iprop(∀ s : S, ∀ target : ITree ε (S × ρ),
    ⌜StateIrel s source.1.car target⌝ -∗
    interp (PROP := PROP) (S := S) s -∗
    wpi H target (fun result => iprop(interp (PROP := PROP) (S := S) result.1 ∗ source.2 result.2)))

instance stateAdequacyPred_ne {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {ε : Type u → Type u} {ρ : Type uρ}
    (H : IHandlerBase PROP ε) :
    NonExpansive (stateAdequacyPred (S := S) (ρ := ρ) H) where
  ne := by
    intro n a b hab
    rcases a with ⟨⟨t₁⟩, Φ₁⟩
    rcases b with ⟨⟨t₂⟩, Φ₂⟩
    obtain rfl := DiscreteO.dist_inj hab.1
    unfold stateAdequacyPred
    exact forall_ne fun s => forall_ne fun target => wand_ne.ne .rfl <|
      wand_ne.ne .rfl <|
        NonExpansive.ne (f := wpi H target) (fun result => sep_ne.ne .rfl (hab.2 result.2))

/-- Return case of state adequacy for any state and postcondition. -/
theorem stateAdequacy_ret {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {ε : Type u → Type u} {ρ : Type uρ}
    (H : IHandlerBase PROP ε) (s : S) (r : ρ) (Φ : ρ → PROP) :
    iprop(interp (PROP := PROP) (S := S) s ∗
      wpi (stateH S ⊕ₕ H) (ret r) Φ) ⊢
    wpi H (ret (s, r))
      (fun result => iprop(interp (PROP := PROP) (S := S) result.1 ∗ Φ result.2)) := by
  rw [wpi_ret, wpi_ret]
  iintro Hboth
  icases Hboth with ⟨Hs, Hpost⟩
  imod Hpost with Hpost
  imodintro
  iframe

/-- Silent-step case: a continuation-level adequacy implication lifts through
one `tau` on both sides without changing the runtime state. -/
theorem stateAdequacy_tau {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {ε : Type u → Type u} {ρ : Type uρ}
    (H : IHandlerBase PROP ε) (s : S)
    (source : ITree (StateE S + ε) ρ) (target : ITree ε (S × ρ))
    (Φ : ρ → PROP)
    (hcont : iprop(interp (PROP := PROP) (S := S) s ∗
      wpi (stateH S ⊕ₕ H) source Φ) ⊢
      wpi H target
        (fun result => iprop(interp (PROP := PROP) (S := S) result.1 ∗ Φ result.2))) :
    iprop(interp (PROP := PROP) (S := S) s ∗
      wpi (stateH S ⊕ₕ H) (tau source) Φ) ⊢
    wpi H (tau target)
      (fun result => iprop(interp (PROP := PROP) (S := S) result.1 ∗ Φ result.2)) := by
  rw [wpi_tau_step, wpi_tau_step]
  iintro Hboth
  icases Hboth with ⟨Hs, Hwp⟩
  imod Hwp with Hwp
  imodintro
  iapply hcont
  iframe

private theorem state_sum_get {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {ε : Type u → Type u}
    (H : IHandlerBase PROP ε) (Φ spawned : S → PROP) :
    (stateH S ⊕ₕ H).handle (SumE.inl StateE.get) Φ spawned = stateHandle StateE.get Φ := rfl

private theorem state_sum_set {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {ε : Type u → Type u}
    (H : IHandlerBase PROP ε) (next : S) (Φ spawned : ULift Unit → PROP) :
    (stateH S ⊕ₕ H).handle (SumE.inl (.set next)) Φ spawned =
      stateHandle (.set next) Φ := rfl

private theorem state_sum_other {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {ε : Type u → Type u}
    (H : IHandlerBase PROP ε) {α : Type u} (e : ε α) (Φ spawned : α → PROP) :
    (stateH S ⊕ₕ H).handle (SumE.inr e) Φ spawned = H.handle e Φ spawned := rfl

/-- Adequacy for arbitrary trees related by `StateIrel`. -/
theorem stateIrel_adequacy_core {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    [BIAffine PROP] {S : Type u} [StateInterp PROP S]
    {ε : Type u → Type u} {ρ : Type uρ}
    (H : IHandlerBase PROP ε) [IHandler.Sequential H]
    (s : S) (source : ITree (StateE S + ε) ρ) (target : ITree ε (S × ρ))
    (hrel : StateIrel s source target) (Φ : ρ → PROP) :
    iprop(interp (PROP := PROP) (S := S) s ∗ wpi (stateH S ⊕ₕ H) source Φ) ⊢
      wpi H target
        (fun result => iprop(interp (PROP := PROP) (S := S) result.1 ∗ Φ result.2)) := by
  iintro Hboth
  icases Hboth with ⟨Hs, Hwp⟩
  ihave Hgen : iprop(∀ st : WpiState PROP (StateE S + ε) ρ,
      wpi (stateH S ⊕ₕ H) st.1.car st.2 -∗ stateAdequacyPred H st) $$ []
  · iapply (wpi_iter (stateH S ⊕ₕ H) (stateAdequacyPred H))
    iintro !> %st HF
    rcases st with ⟨⟨tree⟩, post⟩
    isimp only [stateAdequacyPred]
    iintro %current %out Hrel Hcurrent
    icases Hrel with %h
    have hstep := (StateIrel_unfold current tree out).mp h
    cases hstep with
    | ret r =>
        rw [wpi_ret]
        isimp only [wpiF', wpiF, dest_ret] at HF
        imod HF with HF
        imodintro
        iframe
    | tau child out hchild =>
        rw [wpi_tau_step]
        isimp only [wpiF', wpiF, dest_tau] at HF
        imod HF with HF
        isimp only [stateAdequacyPred] at HF
        imodintro
        iapply HF $$ %current %out %hchild Hcurrent
    | get k out hchild =>
        rw [wpi_tau_step]
        isimp only [wpiF', wpiF, dest_vis, state_sum_get, stateHandle] at HF
        imod HF with HF
        imod HF $$ %current Hcurrent with ⟨Hcurrent, Hcont⟩
        imodintro
        isimp only [stateAdequacyPred] at Hcont
        iapply Hcont $$ %current %out %hchild Hcurrent
    | set next k out hchild =>
        rw [wpi_tau_step]
        isimp only [wpiF', wpiF, dest_vis, state_sum_set, stateHandle] at HF
        imod HF with HF
        imod HF $$ %current Hcurrent with ⟨Hnext, Hcont⟩
        imodintro
        isimp only [stateAdequacyPred] at Hcont
        iapply Hcont $$ %next %out %hchild Hnext
    | vis e k k' hchildren =>
        rw [wpi_vis]
        isimp only [wpiF', wpiF, dest_vis, state_sum_other] at HF
        imod HF with HF
        imodintro
        ihave Hseq : H.handle e
            (fun x => stateAdequacyPred H (⟨⟨k x⟩, post⟩))
            (fun _ => iprop(False)) $$ [HF]
        · iapply IHandler.Sequential.sequential
          iexact HF
        iapply (H.mono e
          (fun x => stateAdequacyPred H (⟨⟨k x⟩, post⟩))
          (fun x => wpi H (k' x)
            (fun result => iprop(interp (PROP := PROP) (S := S) result.1 ∗ post result.2)))
          (fun _ => iprop(False))
          (fun x => fupd ⊤ ∅ (wpi H (k' x) (fun _ => iprop(False))))) $$ [Hcurrent] [] Hseq
        · iintro %x Hcont
          isimp only [stateAdequacyPred] at Hcont
          iapply Hcont $$ %current %(k' x) %(hchildren x) Hcurrent
        · iintro !> %x Hfalse
          iapply false_elim
          iexact Hfalse
  ispecialize Hgen $$ %(⟨⟨source⟩, Φ⟩ : WpiState PROP (StateE S + ε) ρ) Hwp
  isimp only [stateAdequacyPred] at Hgen
  iapply Hgen $$ %s %target %hrel Hs

/-- Masked relational state adequacy, with an arbitrary related target tree. -/
theorem stateIrel_adequacy {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    [BIAffine PROP] {S : Type u} [StateInterp PROP S]
    {ε : Type u → Type u} {ρ : Type uρ}
    (H : IHandlerBase PROP ε) [IHandler.Sequential H]
    (s : S) (source : ITree (StateE S + ε) ρ) (target : ITree ε (S × ρ))
    (hrel : StateIrel s source target) (mask : CoPset) (Φ : ρ → PROP) :
    iprop(interp (PROP := PROP) (S := S) s ∗
      wpiMask (stateH S ⊕ₕ H) mask source Φ) ⊢
    wpiMask H mask target
      (fun result => iprop(interp (PROP := PROP) (S := S) result.1 ∗ Φ result.2)) := by
  iintro Hboth
  icases Hboth with ⟨Hs, Hwp⟩
  unfold wpiMask
  imod Hwp with Hwp
  imodintro
  ihave Hcore : wpi H target
      (fun result => iprop(interp (PROP := PROP) (S := S) result.1 ∗
        |={∅, mask}=> Φ result.2)) $$ [Hs Hwp]
  · iapply (stateIrel_adequacy_core H s source target hrel
      (fun r => iprop(|={∅, mask}=> Φ r)))
    iframe
  iapply (wpi_wand H target
      (fun result => iprop(interp (PROP := PROP) (S := S) result.1 ∗
        |={∅, mask}=> Φ result.2))
      (fun result => iprop(|={∅, mask}=>
        interp (PROP := PROP) (S := S) result.1 ∗ Φ result.2))) $$ [] Hcore
  iintro %result Hpost
  icases Hpost with ⟨Hs, HΦ⟩
  imod HΦ with HΦ
  imodintro
  iframe

/-- Functional execution is one instance of relational state adequacy. -/
theorem stateIfn_adequacy {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    [BIAffine PROP] {S : Type u} [StateInterp PROP S]
    {ε : Type u → Type u} {ρ : Type uρ}
    (H : IHandlerBase PROP ε) [IHandler.Sequential H]
    (s : S) (source : ITree (StateE S + ε) ρ) (mask : CoPset) (Φ : ρ → PROP) :
    iprop(interp (PROP := PROP) (S := S) s ∗
      wpiMask (stateH S ⊕ₕ H) mask source Φ) ⊢
    wpiMask H mask (stateIfn s source)
      (fun result => iprop(interp (PROP := PROP) (S := S) result.1 ∗ Φ result.2)) :=
  stateIrel_adequacy H s source (stateIfn s source) (stateIfn_irel s source) mask Φ

end ProgramLogicCarte
