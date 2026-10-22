import ProgramLogicCarte.State

/-! Ownership-taking state handlers. Ownership appears once next to a wand
that passes it into the continuation. Writes expose the ownership update
rather than assuming it is available for arbitrary interpretations. -/

namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE ITree
universe u uρ w

/-- A read passes owned state to its continuation. A write first updates
ownership, then passes the new ownership to its continuation. -/
def ownershipStateHandle {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {α : Type u}
    (e : StateE S α) (Φ : α → PROP) : PROP :=
  match e with
  | .get => iprop(∃ s : S, interp (PROP := PROP) (S := S) s ∗ (interp (PROP := PROP) (S := S) s -∗ Φ s))
  | .set next => iprop(∃ s : S, interp (PROP := PROP) (S := S) s ∗
      (interp (PROP := PROP) (S := S) s -∗ |={∅}=>
        interp (PROP := PROP) (S := S) next ∗ (interp (PROP := PROP) (S := S) next -∗ Φ (.up ()))))

/-- Logical ownership-threading handler; this is an `IHandlerBase`, not an
interpreter. Spawned-thread continuations are ignored. -/
def ownershipStateH {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    (S : Type u) [StateInterp PROP S] : IHandlerBase PROP (StateE S) where
  handle e Φ _ := ownershipStateHandle e Φ
  mono e := by
    cases e with
    | get =>
        intro Φ Φ' spawned spawned'
        simp only [ownershipStateHandle]
        iintro HΦ _ Hget
        icases Hget with ⟨%s, Hs, Hcont⟩
        iexists s
        iframe Hs
        iintro Hs
        iapply HΦ
        iapply Hcont
        iexact Hs
    | set next =>
        intro Φ Φ' spawned spawned'
        simp only [ownershipStateHandle]
        iintro HΦ _ Hset
        icases Hset with ⟨%s, Hs, Hcont⟩
        iexists s
        iframe Hs
        iintro Hs
        imod Hcont $$ Hs with ⟨Hnext, Hcont⟩
        imodintro
        iframe Hnext
        iintro Hnext
        iapply HΦ
        iapply Hcont
        iexact Hnext
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    cases e with
    | get =>
        simp only [ownershipStateHandle]
        exact BI.exists_ne fun s => sep_ne.ne .rfl (wand_ne.ne .rfl (hΦ s))
    | set next =>
        simp only [ownershipStateHandle]
        exact BI.exists_ne fun s => sep_ne.ne .rfl (wand_ne.ne .rfl
          (fupd_ne.ne (sep_ne.ne .rfl (wand_ne.ne .rfl (hΦ (.up ()))))))

instance ownershipStateHSequential {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    (S : Type u) [StateInterp PROP S] :
    IHandler.Sequential (ownershipStateH (PROP := PROP) S) where
  sequential _ _ _ := .rfl

/-- A read is provable using one actual state token and a continuation
that consumes that token. -/
theorem ownershipStateHandle_get_intro {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] (s : S) (Φ : S → PROP) :
    iprop(interp (PROP := PROP) (S := S) s ∗ (interp (PROP := PROP) (S := S) s -∗ Φ s)) ⊢
      ownershipStateHandle StateE.get Φ := by
  simp only [ownershipStateHandle]
  iintro H
  iexists s
  iexact H

/-- Writes require a concrete ownership update. The update is an assumption
on the interpretation; arbitrary `StateInterp` instances need not permit it. -/
theorem ownershipStateHandle_set_intro {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] (old next : S) (Φ : ULift Unit → PROP)
    (hupdate : interp (PROP := PROP) (S := S) old ⊢ iprop(|={∅}=> interp (PROP := PROP) (S := S) next)) :
    iprop(interp (PROP := PROP) (S := S) old ∗ (interp (PROP := PROP) (S := S) next -∗ Φ (.up ()))) ⊢
      ownershipStateHandle (StateE.set next) Φ := by
  simp only [ownershipStateHandle]
  iintro H
  icases H with ⟨Hold, Hcont⟩
  iexists old
  iframe Hold
  iintro Hold
  imod hupdate $$ Hold with Hnext
  imodintro
  iframe

/-- Two reads use a single ownership token. The residual wand is the
postcondition obligation; no second token is required. -/
theorem ownershipStateHandle_get_get {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] (s : S) (Φ : S → S → PROP) :
    iprop(interp (PROP := PROP) (S := S) s ∗ (interp (PROP := PROP) (S := S) s -∗ Φ s s)) ⊢
      ownershipStateHandle StateE.get (fun first =>
        ownershipStateHandle StateE.get (Φ first)) := by
  simp only [ownershipStateHandle]
  iintro H
  icases H with ⟨Hs, Hcont⟩
  iexists s
  iframe Hs
  iintro Hs
  iexists s
  iframe

/-- The actual two-read WP also needs only one ownership token. -/
theorem wpi_ownership_get_get {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] (s : S) (Φ : S × S → PROP) :
    iprop(interp (PROP := PROP) (S := S) s ∗
      (interp (PROP := PROP) (S := S) s -∗ Φ (s, s))) ⊢
    wpi (ownershipStateH S)
      (vis StateE.get (fun first => vis StateE.get (fun second => ret (first, second)))) Φ := by
  iintro H
  icases H with ⟨Hs, Hcont⟩
  rw [wpi_vis]
  imodintro
  isimp only [ownershipStateH, ownershipStateHandle]
  iexists s
  iframe Hs
  iintro Hs
  rw [wpi_vis]
  imodintro
  isimp only [ownershipStateHandle]
  iexists s
  iframe Hs
  iintro Hs
  rw [wpi_ret]
  imodintro
  iapply Hcont
  iexact Hs

/-- A sufficient ownership law for witness extraction through a continuation
wand. This is a property of the concrete resource model, not a consequence
of the abstract `StateInterp` interface or exclusivity alone. -/
class StateInterpWandChoice (PROP : Type w) [BI PROP] [BIFUpdate PROP]
    (S : Type u) [StateInterp PROP S] : Prop where
  choose : ∀ (s : S) (α : Type u) (Ψ : α → PROP),
    iprop(interp (PROP := PROP) (S := S) s ∗
      (interp (PROP := PROP) (S := S) s -∗ |={∅}=> ∃ a, Ψ a)) ⊢
    iprop(|={∅}=> ∃ a, interp (PROP := PROP) (S := S) s ∗
      (interp (PROP := PROP) (S := S) s -∗ Ψ a))

/-- Intuitionistic state assertions satisfy the choice law by retaining a
copy while applying the continuation. This covers persistent state knowledge;
exclusive full-state ownership requires a separate proof of the choice law. -/
instance stateInterpWandChoiceOfPersistentAffine {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S]
    [∀ s : S, Persistent (interp (PROP := PROP) (S := S) s)]
    [∀ s : S, Affine (interp (PROP := PROP) (S := S) s)] :
    StateInterpWandChoice PROP S where
  choose s α Ψ := by
    iintro H
    icases H with ⟨#Hs, Hcont⟩
    imod Hcont $$ Hs with Hpost
    imodintro
    icases Hpost with ⟨%a, Ha⟩
    iexists a
    iframe Hs
    iintro _
    iexact Ha

/-- Local existential preservation for ownership-threading state operations. -/
theorem ownershipStateHandle_exists {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] [StateInterpWandChoice PROP S]
    {β : Type u} (e : StateE S β) (α : Type u) (Ψ : α → β → PROP) :
    ownershipStateHandle e (fun x => iprop(|={∅}=> ∃ a, Ψ a x)) ⊢
      iprop(|={∅}=> ∃ a, ownershipStateHandle e (Ψ a)) := by
  cases e with
  | get =>
      simp only [ownershipStateHandle]
      iintro H
      icases H with ⟨%s, H⟩
      imod (StateInterpWandChoice.choose s α (fun a => Ψ a s)) $$ H with H
      imodintro
      icases H with ⟨%a, H⟩
      iexists a
      iexists s
      iexact H
  | set next =>
      simp only [ownershipStateHandle]
      iintro H
      icases H with ⟨%old, Hold, Hcont⟩
      ihave Houter : iprop(interp (PROP := PROP) (S := S) old ∗
        (interp (PROP := PROP) (S := S) old -∗ |={∅}=> ∃ a,
          |={∅}=> interp (PROP := PROP) (S := S) next ∗
            (interp (PROP := PROP) (S := S) next -∗ Ψ a (.up ())))) $$ [Hold Hcont]
      · iframe Hold
        iintro Hold
        imod Hcont $$ Hold with Hnext
        imod (StateInterpWandChoice.choose next α (fun a => Ψ a (.up ()))) $$ Hnext with Hnext
        imodintro
        icases Hnext with ⟨%a, Hnext⟩
        iexists a
        imodintro
        iexact Hnext
      imod (StateInterpWandChoice.choose old α (fun a =>
        iprop(|={∅}=> interp (PROP := PROP) (S := S) next ∗
          (interp (PROP := PROP) (S := S) next -∗ Ψ a (.up ()))))) $$ Houter with Houter
      imodintro
      icases Houter with ⟨%a, Houter⟩
      iexists a
      iexists old
      iexact Houter

private def ownershipResultPred {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} {ρ : Type uρ} (state : WpiState PROP (StateE S) ρ) : PROP :=
  iprop(|={∅}=> ∃ r, state.2 r)

private instance ownershipResultPred_ne {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} {ρ : Type uρ} :
    NonExpansive (ownershipResultPred (PROP := PROP) (S := S) (ρ := ρ)) where
  ne := by
    intro n s₁ s₂ hs
    exact fupd_ne.ne (BI.exists_ne hs.2)

private theorem ownershipHandle_eq {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {α : Type u}
    (e : StateE S α) (Φ spawned : α → PROP) :
    (ownershipStateH (PROP := PROP) S).handle e Φ spawned = ownershipStateHandle e Φ := rfl

/-- Logical result extraction for the ownership handler. This does not yet
identify the result with execution from a specified initial state. No
ownership-wand choice or ownership update axiom is needed for this direction. -/
theorem wpi_ownership_result {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {ρ : Type uρ}
    (t : ITree (StateE S) ρ) (Φ : ρ → PROP) :
    wpi (ownershipStateH (PROP := PROP) S) t Φ ⊢ iprop(|={∅}=> ∃ r, Φ r) := by
  iintro Hwp
  ihave Hgen : iprop(∀ state : WpiState PROP (StateE S) ρ,
      wpi (ownershipStateH (PROP := PROP) S) state.1.car state.2 -∗ ownershipResultPred state) $$ []
  · iapply (wpi_iter (ownershipStateH (PROP := PROP) S)
      (ownershipResultPred (PROP := PROP) (S := S) (ρ := ρ)))
    iintro !> %state HF
    rcases state with ⟨⟨tree⟩, post⟩
    isimp only [ownershipResultPred]
    apply tree.dMatchOn
    · intro r ht
      subst tree
      isimp only [wpiF', wpiF, dest_ret] at HF
      imod HF with HF
      imodintro
      iexists r
      iexact HF
    · intro child ht
      subst tree
      isimp only [wpiF', wpiF, dest_tau] at HF
      imod HF with HF
      isimp only [ownershipResultPred] at HF
      iexact HF
    · intro α e k ht
      subst tree
      isimp only [wpiF', wpiF, dest_vis, ownershipHandle_eq] at HF
      imod HF with HF
      cases e with
      | get =>
          isimp only [ownershipStateHandle] at HF
          icases HF with ⟨%s, Hs, Hcont⟩
          ispecialize Hcont $$ Hs
          isimp only [ownershipResultPred] at Hcont
          iexact Hcont
      | set next =>
          isimp only [ownershipStateHandle] at HF
          icases HF with ⟨%s, Hs, Hcont⟩
          imod Hcont $$ Hs with ⟨Hnext, Hcont⟩
          ispecialize Hcont $$ Hnext
          isimp only [ownershipResultPred] at Hcont
          iexact Hcont
  ispecialize Hgen $$ %(⟨⟨t⟩, Φ⟩ : WpiState PROP (StateE S) ρ) Hwp
  isimp only [ownershipResultPred] at Hgen
  iexact Hgen

/-- Pure postcondition extraction. An external adequacy theorem additionally
needs update soundness and a connection to concrete state execution. -/
theorem wpi_ownership_pure_result {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {ρ : Type uρ}
    (t : ITree (StateE S) ρ) (φ : ρ → Prop) :
    wpi (ownershipStateH (PROP := PROP) S) t (fun r => iprop(⌜φ r⌝)) ⊢
      iprop(|={∅}=> ⌜∃ r, φ r⌝) := by
  exact (wpi_ownership_result t (fun r => iprop(⌜φ r⌝))).trans
    (fupd_mono (exists_elim fun r => pure_mono (Exists.intro r)))

/-- External pure-postcondition adequacy, assuming soundness of empty-mask
updates in the chosen BI model. This establishes the postcondition for some
result, not reachability from a specified concrete initial state. -/
theorem ownershipStateH_postcondition_adequacy {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {S : Type u} [StateInterp PROP S] {ρ : Type uρ}
    (hsound : ∀ φ : Prop, (⊢ (iprop(|={∅}=> ⌜φ⌝) : PROP)) → φ)
    (t : ITree (StateE S) ρ) (φ : ρ → Prop)
    (hwp : ⊢ wpi (ownershipStateH (PROP := PROP) S) t (fun r => iprop(⌜φ r⌝))) :
    ∃ r, φ r := by
  exact hsound _ (hwp.trans (wpi_ownership_pure_result t φ))

end ProgramLogicCarte
