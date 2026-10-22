import ProgramLogicCarte.StateOwnership
import ProgramLogicCarte.Void

/-! Authority-linked adequacy for the ownership state handler.

The runtime authority is held by the adequacy proof, not by the program.
The current fragment-only write rule cannot change its state while that
old authority is framed: such a write is inconsistent by agreement.
The joint update below is available to a future operational-step rule;
it does not by itself repair the existing handler's write rule.
-/

namespace ProgramLogicCarte
open Iris Iris.BI Iris.OFE ITree
universe u w uρ

/-- Link program ownership to authoritative runtime state. -/
class StateInterpAuthority (PROP : Type w) [BI PROP] [BIFUpdate PROP]
    (S : Type u) [StateInterp PROP S] where
  auth : S → PROP
  exclusive : ∀ s₁ s₂ : S,
    iprop(interp (PROP := PROP) (S := S) s₁ ∗ interp (PROP := PROP) (S := S) s₂) ⊢ iprop(False)
  agreement : ∀ s₁ s₂ : S,
    iprop(auth s₁ ∗ interp (PROP := PROP) (S := S) s₂) ⊢ iprop(⌜s₁ = s₂⌝)
  update : ∀ old next : S,
    iprop(auth old ∗ interp (PROP := PROP) (S := S) old) ⊢
      iprop(|={∅}=> auth next ∗ interp (PROP := PROP) (S := S) next)

private theorem authority_agreement {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    [BIAffine PROP] {S : Type u} [StateInterp PROP S] [StateInterpAuthority PROP S]
    (s other : S) :
    iprop(StateInterpAuthority.auth (PROP := PROP) s ∗ interp (PROP := PROP) (S := S) other) ⊢
    iprop(⌜s = other⌝ ∧
      (StateInterpAuthority.auth (PROP := PROP) s ∗ interp (PROP := PROP) (S := S) other)) :=
  and_intro (StateInterpAuthority.agreement s other) .rfl

private def authorityAdequacyPred {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] [StateInterpAuthority PROP S] {ρ : Type uρ}
    (state : WpiState PROP (StateE S) ρ) : PROP :=
  iprop(∀ initial : S, StateInterpAuthority.auth (PROP := PROP) initial -∗
    wpi (voidH : IHandlerBase PROP VoidE)
      (stateIfn initial (translate SumE.inl state.1.car))
      (fun result => iprop(StateInterpAuthority.auth (PROP := PROP) result.1 ∗ state.2 result.2)))

private instance authorityAdequacyPred_ne {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] [StateInterpAuthority PROP S] {ρ : Type uρ} :
    NonExpansive (authorityAdequacyPred (PROP := PROP) (S := S) (ρ := ρ)) where
  ne := by
    intro n s₁ s₂ hs
    rcases s₁ with ⟨⟨t₁⟩, Φ₁⟩
    rcases s₂ with ⟨⟨t₂⟩, Φ₂⟩
    obtain rfl := DiscreteO.dist_inj hs.1
    unfold authorityAdequacyPred
    exact forall_ne fun initial => wand_ne.ne .rfl
      (NonExpansive.ne (f := wpi voidH _) (fun result : S × ρ => sep_ne.ne .rfl (hs.2 result.2)))

private theorem fin1Const_zero {α : Type*} (x : α) : fin1Const x 0 = x := rfl

private theorem ownership_handler_eq {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {α : Type u}
    (e : StateE S α) (Φ spawned : α → PROP) :
    (ownershipStateH S).handle e Φ spawned = ownershipStateHandle e Φ := rfl

/-- Logical adequacy against the original state interpreter, preserving
runtime authority at the final state. State-changing writes in the current
handler are ruled out by the framed authority; see the module comment. -/
theorem ownershipStateH_adequacy {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    [BIAffine PROP] {S : Type u} [StateInterp PROP S] [StateInterpAuthority PROP S]
    {ρ : Type uρ} (initial : S) (t : ITree (StateE S) ρ) (Φ : ρ → PROP) :
    iprop(StateInterpAuthority.auth (PROP := PROP) initial ∗ wpi (ownershipStateH S) t Φ) ⊢
    wpi (voidH : IHandlerBase PROP VoidE) (stateIfn initial (translate SumE.inl t))
      (fun result => iprop(StateInterpAuthority.auth (PROP := PROP) result.1 ∗ Φ result.2)) := by
  iintro H
  icases H with ⟨Hauth, Hwp⟩
  ihave Hgen : iprop(∀ state : WpiState PROP (StateE S) ρ,
      wpi (ownershipStateH S) state.1.car state.2 -∗ authorityAdequacyPred state) $$ []
  · iapply (wpi_iter (ownershipStateH S)
      (authorityAdequacyPred (PROP := PROP) (S := S) (ρ := ρ)))
    iintro !> %state HF
    rcases state with ⟨⟨tree⟩, post⟩
    apply tree.dMatchOn
    · intro r ht
      subst tree
      isimp only [authorityAdequacyPred]
      iintro %s Hauth
      rw [translate_ret, stateIfn_ret, wpi_ret]
      isimp only [wpiF', wpiF, dest_ret] at HF
      imod HF with HF
      imodintro
      iframe
    · intro child ht
      subst tree
      isimp only [authorityAdequacyPred]
      iintro %s Hauth
      rw [translate_tau, stateIfn_tau, wpi_tau_step]
      isimp only [wpiF', wpiF, dest_tau] at HF
      imod HF with HF
      imodintro
      isimp only [authorityAdequacyPred, fin1Const_zero] at HF
      ispecialize HF $$ %s Hauth
      iexact HF
    · intro α e k ht
      subst tree
      isimp only [authorityAdequacyPred]
      iintro %s Hauth
      isimp only [wpiF', wpiF, dest_vis, ownership_handler_eq] at HF
      cases e with
      | get =>
          rw [translate_vis, stateIfn_get, wpi_tau_step]
          isimp only [ownershipStateHandle] at HF
          imod HF with HF
          icases HF with ⟨%other, Hfrag, Hcont⟩
          ihave Hboth : iprop(⌜s = other⌝ ∧
              (StateInterpAuthority.auth (PROP := PROP) s ∗ interp (PROP := PROP) (S := S) other)) $$ [Hauth Hfrag]
          · iapply authority_agreement s other
            iframe
          icases Hboth with ⟨%heq, Hauth, Hfrag⟩
          subst other
          ispecialize Hcont $$ Hfrag
          isimp only [authorityAdequacyPred] at Hcont
          imodintro
          iapply Hcont $$ %s Hauth
      | set next =>
          rw [translate_vis, stateIfn_set, wpi_tau_step]
          isimp only [ownershipStateHandle] at HF
          imod HF with HF
          icases HF with ⟨%old, Hfrag, Hcont⟩
          imod Hcont $$ Hfrag with ⟨Hnext, Hcont⟩
          ihave Hboth : iprop(⌜s = next⌝ ∧
              (StateInterpAuthority.auth (PROP := PROP) s ∗ interp (PROP := PROP) (S := S) next)) $$ [Hauth Hnext]
          · iapply authority_agreement s next
            iframe
          icases Hboth with ⟨%heq, Hauth, Hnext⟩
          subst next
          ispecialize Hcont $$ Hnext
          isimp only [authorityAdequacyPred] at Hcont
          imodintro
          iapply Hcont $$ %s Hauth
  ispecialize Hgen $$ %(⟨⟨t⟩, Φ⟩ : WpiState PROP (StateE S) ρ) Hwp
  isimp only [authorityAdequacyPred] at Hgen
  iapply Hgen $$ %initial Hauth

/-- The old authority prevents the current handler's fragment-only write
from changing state. This makes the limitation of the adequacy theorem
explicit rather than silently treating such writes as supported. -/
theorem ownership_write_preserves_authority_state {PROP : Type w}
    [BI PROP] [BIFUpdate PROP] [BIAffine PROP] {S : Type u}
    [StateInterp PROP S] [StateInterpAuthority PROP S]
    (current next : S) (Φ : ULift Unit → PROP) :
    iprop(StateInterpAuthority.auth (PROP := PROP) current ∗
      ownershipStateHandle (StateE.set next) Φ) ⊢ iprop(|={∅}=> ⌜current = next⌝) := by
  iintro H
  icases H with ⟨Hauth, Hset⟩
  isimp only [ownershipStateHandle] at Hset
  icases Hset with ⟨%old, Hfrag, Hcont⟩
  imod Hcont $$ Hfrag with ⟨Hnext, _⟩
  imodintro
  iapply StateInterpAuthority.agreement current next
  iframe

private theorem wpi_tauN_eq {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type u} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (n : Nat) (t : ITree ε ρ) (Φ : ρ → PROP) :
    wpi H (tauN n t) Φ = wpi H t Φ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tauN, ← wpi_tau, ih]

private theorem void_wp_returns {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    [BIAffine PROP] {ρ : Type uρ} (t : ITree (VoidE : Type u → Type u) ρ)
    (Φ : ρ → PROP) :
    wpi (voidH : IHandlerBase PROP VoidE) t Φ ⊢
      iprop(|={∅}=> ∃ n : Nat, ∃ r : ρ, ⌜t = tauN n (ret r)⌝ ∧ Φ r) := by
  classical
  by_cases ht : ∃ n r, t = tauN n (ret r)
  · obtain ⟨n, r, rfl⟩ := ht
    rw [wpi_tauN_eq, wpi_ret]
    iintro Hpost
    imod Hpost with Hpost
    imodintro
    iexists n
    iexists r
    isplit
    · ipureintro
      rfl
    · iexact Hpost
  · have hsilent : SilentlyDiverges t := by
      intro n suffix heq
      apply suffix.dMatchOn
      · intro r hsuffix
        exact False.elim (ht ⟨n, r, heq.trans (congrArg (tauN n) hsuffix)⟩)
      · intro child hsuffix
        exact ⟨child, hsuffix⟩
      · intro α e k hsuffix
        cases e
    exact (wpi_divergence voidH t Φ hsilent).trans (fupd_mono false_elim)

/-- Operational adequacy inside the logic: the original `stateIfn` returns
after finitely many silent steps, and the returned value meets the pure
postcondition. Initialization and update soundness are separated below. -/
theorem ownershipStateH_adequacy_pure {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    [BIAffine PROP] {S : Type u} [StateInterp PROP S] [StateInterpAuthority PROP S]
    {ρ : Type uρ} (initial : S) (t : ITree (StateE S) ρ) (φ : ρ → Prop) :
    iprop(StateInterpAuthority.auth (PROP := PROP) initial ∗
      wpi (ownershipStateH S) t (fun r => iprop(⌜φ r⌝))) ⊢
    iprop(|={∅}=> ⌜∃ n final r,
      stateIfn initial (translate SumE.inl t) =
        tauN n (ret (final, r) : ITree (VoidE : Type u → Type u) (S × ρ)) ∧ φ r⌝) := by
  iintro H
  ihave Hrun : wpi (voidH : IHandlerBase PROP VoidE)
      (stateIfn initial (translate SumE.inl t))
      (fun result => iprop(StateInterpAuthority.auth (PROP := PROP) result.1 ∗ ⌜φ result.2⌝)) $$ [H]
  · iapply ownershipStateH_adequacy initial t (fun r => iprop(⌜φ r⌝))
    iexact H
  imod (void_wp_returns _ _) $$ Hrun with Hrun
  imodintro
  icases Hrun with ⟨%n, %result, Hresult⟩
  icases Hresult with ⟨%heq, _, Hpost⟩
  icases Hpost with %hpost
  ipureintro
  exact ⟨n, result.1, result.2, heq, hpost⟩

/-- External operational adequacy. The caller supplies valid initialization
of runtime authority and the source WP, and soundness of fancy updates in
its concrete BI model. No adequacy assumption about the whole program is
included in `StateInterpAuthority`. -/
theorem ownershipStateH_operational_adequacy {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    [BIAffine PROP] {S : Type u} [StateInterp PROP S] [StateInterpAuthority PROP S]
    {ρ : Type uρ}
    (hsound : ∀ ψ : Prop, (⊢ (iprop(|={∅}=> ⌜ψ⌝) : PROP)) → ψ)
    (initial : S) (t : ITree (StateE S) ρ) (φ : ρ → Prop)
    (hinit : ⊢ iprop(|={∅}=> StateInterpAuthority.auth (PROP := PROP) initial ∗
      wpi (ownershipStateH S) t (fun r => iprop(⌜φ r⌝)))) :
    ∃ n final r, stateIfn initial (translate SumE.inl t) =
      tauN n (ret (final, r) : ITree (VoidE : Type u → Type u) (S × ρ)) ∧ φ r := by
  apply hsound
  exact (hinit.trans (fupd_mono (ownershipStateH_adequacy_pure initial t φ))).trans fupd_idem.mp

end ProgramLogicCarte
