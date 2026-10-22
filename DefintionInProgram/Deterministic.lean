import Iris.BI
import ITree.UpToTaus
import ProgramLogicCarte.Handler
import ProgramLogicCarte.Wpi
import ProgramLogicCarte.AngelicChoice
import ProgramLogicCarte.Step
import ProgramLogicCarte.State
import ProgramLogicCarte.StateOwnership
import ProgramLogicCarte.Void
import ProgramLogicCarte.UndefinedBehavior

open ProgramLogicCarte ITree Iris Iris.BI Iris.OFE ITree

variable {PROP : Type*} [BI PROP] [BIFUpdate PROP] {ε : Type u → Type v} {ρ : Type*}

/-- An existential WP entails an internal witness for the whole WP,
under an empty-mask fancy update. -/
def deterministic
    (t : ITree ε ρ) (H : IHandlerBase PROP ε) : Prop :=
  ∀ (α : Type u) (Φ : α → ρ → PROP),
    ⊢ wpi H t (fun r => iprop(∃ a, Φ a r)) ={∅}=∗
      ∃ a, wpi H t (fun r => Φ a r)

/-- Entailment form of resource-sensitive witness extraction. -/
theorem deterministic_iff_entails (t : ITree ε ρ) (H : IHandlerBase PROP ε) :
    deterministic t H ↔ ∀ (α : Type u) (Φ : α → ρ → PROP),
      wpi H t (fun r => iprop(∃ a, Φ a r)) ⊢
        iprop(|={∅}=> ∃ a, wpi H t (fun r => Φ a r)) := by
  constructor
  · intro hd α Φ
    exact wand_entails (hd α Φ)
  · intro hd α Φ
    iintro Hwp
    iapply hd α Φ
    iexact Hwp

/-- Witness extraction is equivalent to elimination against every common
consequence, retaining the existential WP as a logical resource. -/
theorem deterministic_iff_elim (t : ITree ε ρ) (H : IHandlerBase PROP ε) :
    deterministic t H ↔
      ∀ (α : Type u) (Φ : α → ρ → PROP) (Q : PROP),
        (∀ a, wpi H t (fun r => Φ a r) ⊢ Q) →
          wpi H t (fun r => iprop(∃ a, Φ a r)) ⊢ iprop(|={∅}=> Q) := by
  rw [deterministic_iff_entails]
  constructor
  · intro hd α Φ Q hQ
    exact (hd α Φ).trans (fupd_mono (exists_elim hQ))
  · intro hd α Φ
    apply hd α Φ
    intro a
    iintro Hwp
    iexists a
    iexact Hwp

@[simp]
theorem deterministic_ret {ε : Type u → Type v} {ρ : Type*}
    {r : ρ} {H : IHandlerBase PROP ε} :
    deterministic (ret r) H := by
  apply (deterministic_iff_entails _ _).mpr
  intro α Φ
  simp only [wpi_ret]
  iintro Hpost
  imod Hpost with Hpost
  imodintro
  icases Hpost with ⟨%a, Ha⟩
  iexists a
  imodintro
  iexact Ha

@[simp]
theorem deterministic_tau {ε : Type u → Type v} {ρ : Type*} {t : ITree ε ρ} {H : IHandlerBase PROP ε} :
    deterministic t H → deterministic (tau t) H := by
  simp only [deterministic]
  simp_rw [<-wpi_tau]
  exact id

class DeterministicEff (ε : Type u → Type v) (H : IHandlerBase PROP ε) where
  deterministic : ∀ {ρ : Type*} (t : ITree ε ρ), deterministic t H

instance {H : IHandlerBase PROP VoidE} : DeterministicEff VoidE H where
  deterministic := by
    intro ρ t
    classical
    by_cases ht : ∃ n r, t = tauN n (ret r)
    · obtain ⟨n, r, rfl⟩ := ht
      induction n with
      | zero => exact deterministic_ret
      | succ n ih => exact deterministic_tau ih
    · apply (deterministic_iff_entails _ _).mpr
      intro α Φ
      have hdiv : ∀ n r, t ≠ tauN n (ret r) := by
        intro n r heq
        exact ht ⟨n, r, heq⟩
      have hsilent : ∀ n s, t = tauN n s → ∃ child, s = tau child := by
        intro n s heq
        apply s.dMatchOn
        · intro r hs
          exact False.elim (hdiv n r (heq.trans (congrArg (tauN n) hs)))
        · intro child hs
          exact ⟨child, hs⟩
        · intro α e k hs
          cases e
      exact (wpi_divergence H t _ hsilent).trans (fupd_mono false_elim)

/-- A handler selects one response, with no spawned-thread obligation.
The response assertion can carry resources required by that selection. -/
class WitnessHandler (H : IHandlerBase PROP ε) where
  response : {α : Type u} → ε α → α → PROP
  handle_eq : ∀ {α : Type u} (e : ε α) (Φ spawned : α → PROP),
    H.handle e Φ spawned = iprop(∃ x, response e x ∗ Φ x)

private theorem fin1Const_zero {α : Type*} (x : α) : fin1Const x 0 = x := rfl

private def witnessPred (H : IHandlerBase PROP ε)
    (state : WpiState PROP ε ρ) : PROP :=
  iprop(∀ α : Type u, ∀ Φ : α → ρ → PROP,
    (∀ r, state.2 r -∗ ∃ a, Φ a r) -∗
      |={∅}=> ∃ a, wpi H state.1.car (Φ a))

private instance (H : IHandlerBase PROP ε) :
    NonExpansive (witnessPred (ρ := ρ) H) where
  ne := by
    intro n s₁ s₂ hs
    rcases s₁ with ⟨⟨t₁⟩, post₁⟩
    rcases s₂ with ⟨⟨t₂⟩, post₂⟩
    obtain rfl := DiscreteO.dist_inj hs.1
    unfold witnessPred
    exact forall_ne fun α => forall_ne fun Φ =>
      wand_ne.ne (forall_ne fun r => wand_ne.ne (hs.2 r) .rfl) .rfl

/-- Witness handlers let the postcondition's existential witness be chosen
once for the entire weakest precondition. -/
theorem wpi_exists_of_witness {H : IHandlerBase PROP ε} [WitnessHandler H]
    (t : ITree ε ρ) (α : Type u) (Φ : α → ρ → PROP) :
    wpi H t (fun r => iprop(∃ a, Φ a r)) ⊢
      iprop(|={∅}=> ∃ a, wpi H t (Φ a)) := by
  iintro Hwp
  ihave Hgen : iprop(∀ state : WpiState PROP ε ρ,
      wpi H state.1.car state.2 -∗ witnessPred H state) $$ []
  · iapply (wpi_iter H (witnessPred (ρ := ρ) H))
    iintro !> %state HF
    rcases state with ⟨⟨tree⟩, post⟩
    apply tree.dMatchOn
    · intro r heq
      subst tree
      isimp only [wpiF', wpiF, dest_ret] at HF
      isimp only [witnessPred]
      iintro %α %Φ Hwand
      imod HF with HF
      imodintro
      ispecialize Hwand $$ %r HF
      icases Hwand with ⟨%a, Ha⟩
      iexists a
      rw [wpi_ret]
      imodintro
      iexact Ha
    · intro child heq
      subst tree
      isimp only [wpiF', wpiF, dest_tau] at HF
      isimp only [witnessPred]
      iintro %α %Φ Hwand
      imod HF with HF
      isimp only [witnessPred] at HF
      ispecialize HF $$ %α %Φ Hwand
      imod HF with HF
      imodintro
      icases HF with ⟨%a, Ha⟩
      iexists a
      rw [← wpi_tau]
      isimp only [fin1Const_zero] at Ha
      iexact Ha
    · intro β e k heq
      subst tree
      isimp only [wpiF', wpiF, dest_vis, WitnessHandler.handle_eq] at HF
      isimp only [witnessPred]
      iintro %α %Φ Hwand
      imod HF with HF
      icases HF with ⟨%x, Hresponse, Hchild⟩
      isimp only [witnessPred] at Hchild
      ispecialize Hchild $$ %α %Φ Hwand
      imod Hchild with Hchild
      imodintro
      icases Hchild with ⟨%a, Ha⟩
      iexists a
      rw [wpi_vis, WitnessHandler.handle_eq]
      imodintro
      iexists x
      iframe
  ispecialize Hgen $$ %(⟨⟨t⟩, fun r => iprop(∃ a, Φ a r)⟩ : WpiState PROP ε ρ) Hwp
  isimp only [witnessPred] at Hgen
  ispecialize Hgen $$ %α %Φ
  iapply Hgen
  iintro %r Hr
  iexact Hr

instance (priority := 90) deterministicEffOfWitness
    {H : IHandlerBase PROP ε} [WitnessHandler H] : DeterministicEff ε H where
  deterministic := by
    intro ρ t
    apply (deterministic_iff_entails _ _).mpr
    intro α Φ
    exact wpi_exists_of_witness t α Φ

instance witnessHandlerVoid {H : IHandlerBase PROP VoidE} : WitnessHandler H where
  response e := nomatch e
  handle_eq e := nomatch e

instance witnessHandlerAngelic : WitnessHandler (angelicH : IHandlerBase PROP AngelicE) where
  response _ _ := emp
  handle_eq e Φ spawned := by
    cases e
    simp only [angelicH, emp_sep.to_eq]

instance witnessHandlerUb : WitnessHandler (ubH : IHandlerBase PROP UbE) where
  response _ _ := emp
  handle_eq e Φ spawned := by
    cases e
    simp only [ubH, emp_sep.to_eq]
    apply BIBase.BiEntails.to_eq
    constructor
    · exact false_elim
    · iintro H
      icases H with ⟨%x, Hx⟩
      exact Empty.elim x.down

instance witnessHandlerStepIdentity :
    WitnessHandler (stepH .identity : IHandlerBase PROP StepE) where
  response _ _ := emp
  handle_eq e Φ spawned := by
    cases e
    simp only [stepH, stepHandle, lat, emp_sep.to_eq]
    apply BIBase.BiEntails.to_eq
    constructor
    · iintro H
      iexists ULift.up ()
      iexact H
    · iintro H
      icases H with ⟨%x, Hx⟩
      cases x with
      | up x => cases x; iexact Hx

instance witnessHandlerSum {ε₁ ε₂ : Type u → Type v}
    (H₁ : IHandlerBase PROP ε₁) (H₂ : IHandlerBase PROP ε₂)
    [WitnessHandler H₁] [WitnessHandler H₂] : WitnessHandler (H₁ ⊕ₕ H₂) where
  response e := match e with
    | .inl e => WitnessHandler.response (H := H₁) e
    | .inr e => WitnessHandler.response (H := H₂) e
  handle_eq e Φ spawned := by
    cases e with
    | inl e => exact WitnessHandler.handle_eq e Φ spawned (H := H₁)
    | inr e => exact WitnessHandler.handle_eq e Φ spawned (H := H₂)


/-- State execution is deterministic once its initial state is fixed.
Both the final state and the return value are retained in the result. -/
theorem deterministic_state_execution {S : Type u} (initial : S)
    (t : ITree (StateE S + VoidE) ρ) :
    deterministic (stateIfn initial t) (voidH : IHandlerBase PROP VoidE) :=
  DeterministicEff.deterministic (stateIfn initial t)

/-- Transfer determinism to a logical state handler when its weakest
preconditions agree with execution from a specified initial state. -/
theorem deterministic_stateH_of_execution {S : Type u} [StateInterp PROP S]
    (initial : S) (t : ITree (StateE S) ρ)
    (hwp : ∀ Ψ : ρ → PROP,
      wpi (stateH (PROP := PROP) S) t Ψ =
        wpi (voidH : IHandlerBase PROP VoidE)
          (stateIfn initial (translate SumE.inl t)) (fun result => Ψ result.2)) :
    deterministic t (stateH (PROP := PROP) S) := by
  intro α Φ
  have hd := deterministic_state_execution (PROP := PROP) initial (translate SumE.inl t)
  simpa only [hwp] using hd α (fun a result => Φ a result.2)

/-- State determinism is relative to a fixed initial state. The state
interpreter removes state effects while retaining the final state. -/
def deterministicState {S : Type u} (initial : S)
    (t : ITree (StateE S) ρ) : Prop :=
  deterministic (stateIfn initial (translate SumE.inl t))
    (voidH : IHandlerBase PROP VoidE)

/-- Reads and writes are deterministic for every fixed initial state. -/
theorem deterministic_state {S : Type u} (initial : S)
    (t : ITree (StateE S) ρ) : deterministicState (PROP := PROP) initial t :=
  deterministic_state_execution initial (translate SumE.inl t)

/-- Every state program is deterministic relative to its initial state. -/
class DeterministicStateEff (PROP : Type*) [BI PROP] [BIFUpdate PROP]
    (S : Type u) : Prop where
  deterministic : ∀ {ρ : Type*} (initial : S) (t : ITree (StateE S) ρ),
    deterministicState (PROP := PROP) initial t

instance deterministicStateEff {S : Type u} : DeterministicStateEff PROP S where
  deterministic := deterministic_state

/-- A local sufficient condition on the interpretation of state ownership.
Existential witnesses can be selected uniformly across all initial states,
including after an empty-mask update. This is an additional choice law;
it does not follow merely from exclusivity or agreement of state ownership. -/
class StateInterpUniformChoice (PROP : Type*) [BI PROP] [BIFUpdate PROP]
    (S : Type u) [StateInterp PROP S] : Prop where
  choose : ∀ {β : Type u} (e : StateE S β) (α : Type u) (Ψ : α → β → PROP),
    stateHandle e (fun x => iprop(|={∅}=> ∃ a, Ψ a x)) ⊢
      iprop(|={∅}=> ∃ a, stateHandle e (Ψ a))

private theorem stateH_handle {S : Type u} [StateInterp PROP S]
    {β : Type u} (e : StateE S β) (Ψ spawned : β → PROP) :
    (stateH S).handle e Ψ spawned = stateHandle e Ψ := rfl

/-- Uniform choice for state operations lifts to the whole weakest precondition. -/
theorem wpi_exists_of_state {S : Type u} [StateInterp PROP S]
    [StateInterpUniformChoice PROP S]
    (t : ITree (StateE S) ρ) (α : Type u) (Φ : α → ρ → PROP) :
    wpi (stateH S) t (fun r => iprop(∃ a, Φ a r)) ⊢
      iprop(|={∅}=> ∃ a, wpi (stateH S) t (Φ a)) := by
  iintro Hwp
  ihave Hgen : iprop(∀ state : WpiState PROP (StateE S) ρ,
      wpi (stateH S) state.1.car state.2 -∗ witnessPred (stateH S) state) $$ []
  · iapply (wpi_iter (stateH S) (witnessPred (ρ := ρ) (stateH S)))
    iintro !> %state HF
    rcases state with ⟨⟨tree⟩, post⟩
    apply tree.dMatchOn
    · intro r heq
      subst tree
      isimp only [wpiF', wpiF, dest_ret] at HF
      isimp only [witnessPred]
      iintro %α %Φ Hwand
      imod HF with HF
      imodintro
      ispecialize Hwand $$ %r HF
      icases Hwand with ⟨%a, Ha⟩
      iexists a
      rw [wpi_ret]
      imodintro
      iexact Ha
    · intro child heq
      subst tree
      isimp only [wpiF', wpiF, dest_tau] at HF
      isimp only [witnessPred]
      iintro %α %Φ Hwand
      imod HF with HF
      isimp only [witnessPred] at HF
      ispecialize HF $$ %α %Φ Hwand
      imod HF with HF
      imodintro
      icases HF with ⟨%a, Ha⟩
      iexists a
      rw [← wpi_tau]
      isimp only [fin1Const_zero] at Ha
      iexact Ha
    · intro β e k heq
      subst tree
      isimp only [wpiF', wpiF, dest_vis, stateH_handle] at HF
      isimp only [witnessPred]
      iintro %α %Φ Hwand
      imod HF with HF
      ihave Hchoice : stateHandle e (fun x =>
          iprop(|={∅}=> ∃ a, wpi (stateH S) (k x) (Φ a))) $$ [Hwand HF]
      · have hmono := (stateH (PROP := PROP) S).mono e
          (fun x => witnessPred (stateH S) (⟨⟨k x⟩, post⟩))
          (fun x => iprop(|={∅}=> ∃ a, wpi (stateH S) (k x) (Φ a)))
          (fun _ => iprop(False)) (fun _ => iprop(False))
        simp only [stateH_handle] at hmono
        iapply hmono $$ [Hwand] [] HF
        · iintro %x Hchild
          isimp only [witnessPred] at Hchild
          ispecialize Hchild $$ %α %Φ Hwand
          iexact Hchild
        · iintro !> %x Hfalse
          iexact Hfalse
      imod (StateInterpUniformChoice.choose e α
        (fun a x => wpi (stateH S) (k x) (Φ a))) $$ Hchoice with Hchoice
      imodintro
      icases Hchoice with ⟨%a, Ha⟩
      iexists a
      rw [wpi_vis]
      imodintro
      isimp only [stateH_handle]
      iexact Ha
  ispecialize Hgen $$ %(⟨⟨t⟩, fun r => iprop(∃ a, Φ a r)⟩ : WpiState PROP (StateE S) ρ) Hwp
  isimp only [witnessPred] at Hgen
  ispecialize Hgen $$ %α %Φ
  iapply Hgen
  iintro %r Hr
  iexact Hr


instance deterministicEffStateH {S : Type u} [StateInterp PROP S]
    [StateInterpUniformChoice PROP S] :
    DeterministicEff (StateE S) (stateH (PROP := PROP) S) where
  deterministic := by
    intro ρ t
    apply (deterministic_iff_entails _ _).mpr
    intro α Φ
    exact wpi_exists_of_state t α Φ

private theorem ownershipStateH_handle {S : Type u} [StateInterp PROP S]
    {β : Type u} (e : StateE S β) (Ψ spawned : β → PROP) :
    (ownershipStateH S).handle e Ψ spawned = ownershipStateHandle e Ψ := rfl

/-- Ownership-wand choice for state operations lifts to the whole weakest precondition. -/
theorem wpi_exists_of_ownership_state {S : Type u} [StateInterp PROP S]
    [StateInterpWandChoice PROP S]
    (t : ITree (StateE S) ρ) (α : Type u) (Φ : α → ρ → PROP) :
    wpi (ownershipStateH S) t (fun r => iprop(∃ a, Φ a r)) ⊢
      iprop(|={∅}=> ∃ a, wpi (ownershipStateH S) t (Φ a)) := by
  iintro Hwp
  ihave Hgen : iprop(∀ state : WpiState PROP (StateE S) ρ,
      wpi (ownershipStateH S) state.1.car state.2 -∗ witnessPred (ownershipStateH S) state) $$ []
  · iapply (wpi_iter (ownershipStateH S) (witnessPred (ρ := ρ) (ownershipStateH S)))
    iintro !> %state HF
    rcases state with ⟨⟨tree⟩, post⟩
    apply tree.dMatchOn
    · intro r heq
      subst tree
      isimp only [wpiF', wpiF, dest_ret] at HF
      isimp only [witnessPred]
      iintro %α %Φ Hwand
      imod HF with HF
      imodintro
      ispecialize Hwand $$ %r HF
      icases Hwand with ⟨%a, Ha⟩
      iexists a
      rw [wpi_ret]
      imodintro
      iexact Ha
    · intro child heq
      subst tree
      isimp only [wpiF', wpiF, dest_tau] at HF
      isimp only [witnessPred]
      iintro %α %Φ Hwand
      imod HF with HF
      isimp only [witnessPred] at HF
      ispecialize HF $$ %α %Φ Hwand
      imod HF with HF
      imodintro
      icases HF with ⟨%a, Ha⟩
      iexists a
      rw [← wpi_tau]
      isimp only [fin1Const_zero] at Ha
      iexact Ha
    · intro β e k heq
      subst tree
      isimp only [wpiF', wpiF, dest_vis, ownershipStateH_handle] at HF
      isimp only [witnessPred]
      iintro %α %Φ Hwand
      imod HF with HF
      ihave Hchoice : ownershipStateHandle e (fun x =>
          iprop(|={∅}=> ∃ a, wpi (ownershipStateH S) (k x) (Φ a))) $$ [Hwand HF]
      · have hmono := (ownershipStateH (PROP := PROP) S).mono e
          (fun x => witnessPred (ownershipStateH S) (⟨⟨k x⟩, post⟩))
          (fun x => iprop(|={∅}=> ∃ a, wpi (ownershipStateH S) (k x) (Φ a)))
          (fun _ => iprop(False)) (fun _ => iprop(False))
        simp only [ownershipStateH_handle] at hmono
        iapply hmono $$ [Hwand] [] HF
        · iintro %x Hchild
          isimp only [witnessPred] at Hchild
          ispecialize Hchild $$ %α %Φ Hwand
          iexact Hchild
        · iintro !> %x Hfalse
          iexact Hfalse
      imod (ownershipStateHandle_exists e α
        (fun a x => wpi (ownershipStateH S) (k x) (Φ a))) $$ Hchoice with Hchoice
      imodintro
      icases Hchoice with ⟨%a, Ha⟩
      iexists a
      rw [wpi_vis]
      imodintro
      isimp only [ownershipStateH_handle]
      iexact Ha
  ispecialize Hgen $$ %(⟨⟨t⟩, fun r => iprop(∃ a, Φ a r)⟩ : WpiState PROP (StateE S) ρ) Hwp
  isimp only [witnessPred] at Hgen
  ispecialize Hgen $$ %α %Φ
  iapply Hgen
  iintro %r Hr
  iexact Hr


/-- The ownership-threading logical handler extracts internal WP witnesses
when its state assertions satisfy ownership-wand choice. -/
instance deterministicEffOwnershipStateH {S : Type u} [StateInterp PROP S]
    [StateInterpWandChoice PROP S] :
    DeterministicEff (StateE S) (ownershipStateH (PROP := PROP) S) where
  deterministic := by
    intro ρ t
    apply (deterministic_iff_entails _ _).mpr
    intro α Φ
    exact wpi_exists_of_ownership_state t α Φ
