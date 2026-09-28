import Iris.BI.Lib.Fixpoint
import Iris.Instances.Lib.FUpd
import ProgramLogicCarte.Handler
import ITree.Basic

/-!
# Weakest preconditions for interaction trees

This file translates the fixed-point construction in `src/wpi.v`.  The tree
itself carries the discrete OFE, while postconditions carry Iris' pointwise
OFE.  Consequently the least fixed point is available without imposing an
OFE structure on interaction trees.
-/

namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE ITree

universe u v uρ w

abbrev WpiState (PROP : Type w) [BI PROP] (ε : Type u → Type v) (ρ : Type uρ) :=
  DiscreteO (ITree ε ρ) × (ρ → PROP)

/-- One unfolding of the interaction-tree weakest precondition. -/
def wpiF {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (wpi : ITree ε ρ → (ρ → PROP) → PROP)
    (t : ITree ε ρ) (Φ : ρ → PROP) : PROP :=
  match t.dest with
  | ⟨.ret r, _⟩ => fupd ∅ ∅ (Φ r)
  | ⟨.tau, k⟩ => fupd ∅ ∅ (wpi (k 0) Φ)
  | ⟨.vis _ e, k⟩ =>
      fupd ∅ ∅ (H.handle e
        (fun a => wpi (k a) Φ)
        (fun a => fupd ⊤ ∅ (wpi (k a) (fun _ => iprop(False)))))

/-- Uncurried form used by Iris' least-fixed-point construction. -/
def wpiF' {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (rec : WpiState PROP ε ρ → PROP) : WpiState PROP ε ρ → PROP
  | (⟨t⟩, Φ) => wpiF H (fun t Φ => rec (⟨t⟩, Φ)) t Φ

instance wpiF_mono {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε) :
    BIMonoPred (wpiF' (ρ := ρ) H) where
  mono_pred := by
    intro rec rec' hrec hrec'
    iintro #Hrec %state HF
    rcases state with ⟨⟨t⟩, Φ⟩
    apply t.dMatchOn
    · intro r ht
      subst t
      isimp only [wpiF', wpiF, dest_ret] at HF
      isimp only [wpiF', wpiF, dest_ret]
      iexact HF
    · intro child ht
      subst t
      isimp only [wpiF', wpiF, dest_tau] at HF
      isimp only [wpiF', wpiF, dest_tau]
      imod HF with HF
      imodintro
      iapply Hrec $$ HF
    · intro α e k ht
      subst t
      isimp only [wpiF', wpiF, dest_vis] at HF
      isimp only [wpiF', wpiF, dest_vis]
      imod HF with HF
      imodintro
      iapply (H.mono e
        (fun a => rec (⟨k a⟩, Φ))
        (fun a => rec' (⟨k a⟩, Φ))
        (fun a => fupd ⊤ ∅ (rec (⟨k a⟩, fun _ => iprop(False))))
        (fun a => fupd ⊤ ∅ (rec' (⟨k a⟩, fun _ => iprop(False)))))
      · iintro %a Ha
        iapply Hrec $$ Ha
      · iintro !> %a Ha
        imod Ha with Ha
        imodintro
        iapply Hrec $$ Ha
      · iexact HF
  mono_pred_ne := by
    intro rec hrec
    constructor
    intro n state₁ state₂ hstate
    rcases state₁ with ⟨⟨t₁⟩, Φ₁⟩
    rcases state₂ with ⟨⟨t₂⟩, Φ₂⟩
    rcases hstate with ⟨ht, hΦ⟩
    obtain rfl := DiscreteO.dist_inj ht
    apply t₁.dMatchOn
    · intro r ht
      subst t₁
      simp only [wpiF', wpiF, dest_ret]
      exact BIFUpdate.ne.ne (hΦ r)
    · intro t ht
      subst t₁
      simp only [wpiF', wpiF, dest_tau]
      refine BIFUpdate.ne.ne (NonExpansive.ne ?_)
      exact ⟨.rfl, hΦ⟩
    · intro α e k ht
      subst t₁
      simp only [wpiF', wpiF, dest_vis]
      refine BIFUpdate.ne.ne (H.ne (n := n) e
        (Φ₁ := fun a => rec (⟨k a⟩, Φ₁))
        (Φ₂ := fun a => rec (⟨k a⟩, Φ₂))
        (spawned₁ := fun a => fupd ⊤ ∅ (rec (⟨k a⟩, fun _ => iprop(False))))
        (spawned₂ := fun a => fupd ⊤ ∅ (rec (⟨k a⟩, fun _ => iprop(False))))
        ?_ ?_)
      · intro a
        apply NonExpansive.ne (f := rec)
        constructor
        · exact OFE.Dist.rfl
        · exact hΦ
      · intro a
        exact BIFUpdate.ne.ne (NonExpansive.ne (f := rec) OFE.Dist.rfl)

/-- Weakest precondition for an interaction tree under logical handler `H`. -/
def wpi {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (t : ITree ε ρ) (Φ : ρ → PROP) : PROP :=
  bi_least_fixpoint (wpiF' H) (⟨t⟩, Φ)

/-- Hoare triple for an interaction tree under handler `H`. -/
macro:25 "{{{" P:term "}}}" t:term "@@" H:term "{{{" Q:term "}}}" : term =>
  `(iprop($P -∗ wpi $H $t $Q))

instance wpi_ne {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (t : ITree ε ρ) : NonExpansive (wpi H t) where
  ne {n Φ₁ Φ₂} hΦ := by
    refine NonExpansive.ne (f := bi_least_fixpoint (wpiF' H)) ?_
    exact ⟨.rfl, hΦ⟩

/-- Unfold the least fixed point once. -/
theorem wpi_unfold {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (t : ITree ε ρ) (Φ : ρ → PROP) :
    wpi H t Φ = wpiF H (wpi H) t Φ := by
  exact least_fixpoint_unfold (wpiF' H)

@[simp]
theorem wpi_ret {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (r : ρ) (Φ : ρ → PROP) :
    wpi H (ret r) Φ = iprop(|={∅}=> Φ r) := by
  rw [wpi_unfold]
  rfl

@[simp]
theorem wpi_tau_step {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (t : ITree ε ρ) (Φ : ρ → PROP) :
    wpi H (tau t) Φ = iprop(|={∅}=> wpi H t Φ) := by
  rw [wpi_unfold]
  rfl

/-- A silent step is logically invisible.  The second unfolding is needed
because the definition itself starts with an empty-mask fancy update. -/
theorem wpi_tau {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (t : ITree ε ρ) (Φ : ρ → PROP) :
    wpi H t Φ = wpi H (tau t) Φ := by
  rw [wpi_tau_step, wpi_unfold]
  apply t.dMatchOn
  · intro r ht
    subst t
    simp only [wpiF, dest_ret]
    exact fupd_idem.to_eq.symm
  · intro child ht
    subst t
    simp only [wpiF, dest_tau]
    exact fupd_idem.to_eq.symm
  · intro α e k ht
    subst t
    simp only [wpiF, dest_vis]
    exact fupd_idem.to_eq.symm

@[simp]
theorem wpi_vis {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    {α : Type u} (e : ε α) (k : α → ITree ε ρ) (Φ : ρ → PROP) :
    wpi H (vis e k) Φ = iprop(
      |={∅}=> H.handle e
        (fun a => wpi H (k a) Φ)
        (fun a => fupd ⊤ ∅ (wpi H (k a) (fun _ => iprop(False))))) := by
  rw [wpi_unfold]
  rfl

/-- Masked weakest precondition from Coq `wpi_mask`: open the chosen mask
before executing the empty-mask tree, and restore it for the postcondition. -/
def wpiMask {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (mask : CoPset) (t : ITree ε ρ) (Φ : ρ → PROP) : PROP :=
  iprop(|={mask, ∅}=> wpi H t (fun result => iprop(|={∅, mask}=> Φ result)))

/-- Returning a value is valid under any invariant mask. -/
theorem wpiMask_ret {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (mask : CoPset) (value : ρ) (Φ : ρ → PROP) :
    Φ value ⊢ wpiMask H mask (ret value) Φ := by
  rw [wpiMask, wpi_ret]
  istart
  iintro HΦ
  iapply (fupd_mono (fupd_intro (E := (∅ : CoPset))))
  iapply fupd_mask_intro_subseteq Std.LawfulSet.empty_subset
  iexact HΦ

/-- Iteration principle for `wpi`, directly exposing least-fixed-point
iteration on the uncurried state space. -/
theorem wpi_iter {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (G : WpiState PROP ε ρ → PROP) [NonExpansive G] :
    ⊢ iprop(
      □ (∀ state, wpiF' H G state -∗ G state) -∗
      ∀ state, wpi H state.1.car state.2 -∗ G state) := by
  exact least_fixpoint_iter (wpiF' H)

/-- Fixed-point induction principle.  Recursive calls provide both the
induction hypothesis and the original `wpi`. -/
theorem wpi_induction {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandlerBase PROP ε)
    (G : WpiState PROP ε ρ → PROP) [NonExpansive G] :
    ⊢ iprop(
      □ (∀ state,
        wpiF' H (fun next => iprop(G next ∧ wpi H next.1.car next.2)) state -∗
        G state) -∗
      ∀ state, wpi H state.1.car state.2 -∗ G state) := by
  exact least_fixpoint_ind (wpiF' H) G

end ProgramLogicCarte
