import ProgramLogicCarte.HeapAdequacy

/-! Heap operations for the finite-map heap and the standard state handler. -/

namespace ProgramLogicCarte.HeapLogic

open Iris Iris.BI ITree Iris.Std Iris.Std.PartialMap

/-- An absent cell and a freed cell both return `none`, but only the latter
has a points-to fragment. -/
def load {V : Type} (location : Nat) : ITree (HeapE V) (Option V) :=
  (getState (fun e => e)).bind fun heap => ret ((get? (M := HeapMap) heap location).join)

/-- Replace a cell and return its old optional value. The write rule below
requires ownership of an existing cell; inserting at a missing key is not
covered by that rule. -/
def store' {V : Type} (location : Nat) (value : Option V) :
    ITree (HeapE V) (Option V) :=
  (getState (fun e => e)).bind fun heap =>
    (setState (fun e => e) (Iris.Std.insert (M := HeapMap) heap location value)).bind fun _ =>
      ret ((get? (M := HeapMap) heap location).join)

def store {V : Type} (location : Nat) (value : V) : ITree (HeapE V) (Option V) :=
  store' location (some value)

def free {V : Type} (location : Nat) : ITree (HeapE V) (Option V) :=
  store' location none

section Rules

variable {V : Type} {GF : BundledGFunctors} {hlc : HasLC}
variable [InvGS_gen hlc GF] [GhostMapG GF Nat (Option V) HeapMap]

/-- Agreement between the runtime heap and a fractional fragment. -/
theorem heapState_lookup (N : Namespace) (γ : GName) (heap : Heap V)
    (location : Nat) (dq : DFrac) (value : Option V) :
    iprop(heapState (V := V) (GF := GF) N γ heap ∗ pointsTo γ location dq value) ⊢
      iprop(⌜get? (M := HeapMap) heap location = some value⌝ ∧
        (heapState N γ heap ∗ pointsTo γ location dq value)) := by
  apply and_intro ?_ .rfl
  iintro ⟨Hstate, Hcell⟩
  isimp only [heapState] at Hstate
  ihave Hauth := and_elim_l $$ Hstate
  isimp only [pointsTo] at Hcell
  iapply ghost_map_lookup $$ Hauth Hcell

/-- The ordinary state handler reads without consuming the cell fragment. -/
theorem wpi_load (N : Namespace) (γ : GName) (location : Nat)
    (dq : DFrac) (value : Option V) (Φ : Option V → IProp GF) :
    iprop(pointsTo γ location dq value ∗
      (pointsTo γ location dq value -∗ Φ value)) ⊢
      wpi (heapH (V := V) N γ) (load location) Φ := by
  iintro ⟨Hcell, Hcont⟩
  rw [load, getState, trigger, ITree.bind_vis, wpi_vis]
  imodintro
  isimp only [heapH, stateH, stateHandle]
  iintro %heap Hstate
  ihave ⟨%hlookup, Hstate, Hcell⟩ :=
    heapState_lookup N γ heap location dq value $$ [$Hstate $Hcell]
  imodintro
  iframe Hstate
  rw [ITree.bind_ret, hlookup, Option.join_some, wpi_ret]
  imodintro
  iapply Hcont $$ Hcell

/-- Masked read rule: fractional ownership must describe a present map key,
including when its stored value is `none`. -/
theorem wpiMask_load (N : Namespace) (γ : GName) (mask : CoPset)
    (location : Nat) (dq : DFrac) (value : Option V) (Φ : Option V → IProp GF) :
    iprop(pointsTo γ location dq value ∗
      (pointsTo γ location dq value -∗ Φ value)) ⊢
      wpiMask (heapH (V := V) N γ) mask (load location) Φ := by
  iintro ⟨Hcell, Hcont⟩
  unfold wpiMask
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hrestore
  iapply wpi_load N γ location dq value
  iframe Hcell
  iintro Hcell
  imod Hrestore
  iapply Hcont $$ Hcell

/-- A present cell can be read repeatedly without changing its fragment. -/
theorem wpiMask_load_spec (N : Namespace) (γ : GName) (mask : CoPset)
    (location : Nat) (dq : DFrac) (value : Option V) :
    pointsTo (V := V) (GF := GF) γ location dq value ⊢
      wpiMask (heapH (V := V) N γ) mask (load location)
        (fun result => iprop(⌜result = value⌝ ∗ pointsTo γ location dq value)) := by
  iintro Hcell
  iapply wpiMask_load N γ mask location dq value
  iframe Hcell
  iintro Hcell
  iframe Hcell
  itrivial

private theorem heapState_as_half (N : Namespace) (γ : GName) (heap : Heap V) :
    heapState (V := V) (GF := GF) N γ heap =
      iprop(ghost_map_auth (H := HeapMap) γ (.own ((1 : Qp).half)) heap ∧
        heapInv (V := V) N γ) := by
  rfl

private theorem heapInv_as_half (N : Namespace) (γ : GName) :
    heapInv (V := V) (GF := GF) N γ =
      inv N (iprop(∃ heap : Heap V,
        ghost_map_auth (H := HeapMap) γ (.own ((1 : Qp).half)) heap)) := by
  rfl

private def authHalf : DFrac := .own ((1 : Qp).half)

/-- Updating a present cell while holding both authority halves. The two
halves must be reunited before `ghost_map_update` and split afterwards. -/
theorem two_halves_update (γ : GName) (heap : Heap V) (location : Nat)
    (old next : Option V) :
    iprop(ghost_map_auth (GF := GF) (H := HeapMap) γ authHalf heap ∗
      ghost_map_auth (H := HeapMap) γ authHalf heap ∗
      pointsTo γ location (.own 1) old) ⊢
    iprop(|={∅}=> ghost_map_auth (H := HeapMap) γ authHalf
        (Iris.Std.insert (M := HeapMap) heap location next) ∗
      ghost_map_auth (H := HeapMap) γ authHalf
        (Iris.Std.insert (M := HeapMap) heap location next) ∗
      pointsTo γ location (.own 1) next) := by
  have hsplit (m : Heap V) :
      (ghost_map_auth (H := HeapMap) γ (.own (1 : Qp)) m : IProp GF) ⊣⊢
        iprop(ghost_map_auth (H := HeapMap) γ authHalf m ∗
          ghost_map_auth (H := HeapMap) γ authHalf m) := by
    simpa only [authHalf, Qp.half_add_half] using
      (Fractional.fractional (PROP := IProp GF)
        (Φ := fun q => ghost_map_auth (H := HeapMap) γ (.own q) m)
        (1 : Qp).half (1 : Qp).half)
  iintro ⟨Ha, Hb, Hcell⟩
  ihave Hauth := (hsplit heap).mpr $$ [$Ha $Hb]
  isimp only [pointsTo] at Hcell
  imod ghost_map_update next $$ Hauth Hcell with ⟨Hauth, Hcell⟩
  imodintro
  icases (hsplit (Iris.Std.insert (M := HeapMap) heap location next)).mp $$ Hauth with
    ⟨Ha, Hb⟩
  isimp only [pointsTo]
  iframe

private theorem two_halves_update_explicit (γ : GName) (heap : Heap V)
    (location : Nat) (old next : Option V) :
    iprop(ghost_map_auth (GF := GF) (H := HeapMap) γ (.own ((1 : Qp).half)) heap ∗
      ghost_map_auth (H := HeapMap) γ (.own ((1 : Qp).half)) heap ∗
      pointsTo γ location (.own 1) old) ⊢
    iprop(|={∅}=> ghost_map_auth (H := HeapMap) γ (.own ((1 : Qp).half))
        (Iris.Std.insert (M := HeapMap) heap location next) ∗
      ghost_map_auth (H := HeapMap) γ (.own ((1 : Qp).half))
        (Iris.Std.insert (M := HeapMap) heap location next) ∗
      pointsTo γ location (.own 1) next) := by
  simpa only [authHalf] using two_halves_update γ heap location old next

/-- Agreement without consuming either authority half. -/
private theorem halves_agree (γ : GName) (left right : Heap V) :
    iprop(ghost_map_auth (GF := GF) (H := HeapMap) γ (.own ((1 : Qp).half)) left ∗
      ghost_map_auth (H := HeapMap) γ (.own ((1 : Qp).half)) right) ⊢
      iprop(⌜left = right⌝ ∧
        (ghost_map_auth (H := HeapMap) γ (.own ((1 : Qp).half)) left ∗
         ghost_map_auth (H := HeapMap) γ (.own ((1 : Qp).half)) right)) := by
  apply and_intro ?_ .rfl
  iintro ⟨Ha, Hb⟩
  iapply (ghost_map_auth_agree (H := HeapMap) γ (.own ((1 : Qp).half)) (.own ((1 : Qp).half)) left right) $$ Ha Hb

private theorem state_from_half (N : Namespace) (γ : GName) (heap : Heap V) :
    iprop(ghost_map_auth (GF := GF) (H := HeapMap) γ (.own ((1 : Qp).half)) heap ∗
      inv N (iprop(∃ current : Heap V,
        ghost_map_auth (H := HeapMap) γ (.own ((1 : Qp).half)) current))) ⊢
    heapState N γ heap := by
  rw [heapState_as_half, heapInv_as_half]
  iintro ⟨Ha, Hinv⟩
  isplit
  · iexact Ha
  · iexact Hinv

private theorem half_lookup (γ : GName) (heap : Heap V) (location : Nat)
    (old : Option V) :
    iprop(ghost_map_auth (GF := GF) (H := HeapMap) γ (.own ((1 : Qp).half)) heap ∗
      pointsTo γ location (.own 1) old) ⊢
      iprop(⌜get? (M := HeapMap) heap location = some old⌝ ∧
        (ghost_map_auth (H := HeapMap) γ (.own ((1 : Qp).half)) heap ∗
          pointsTo γ location (.own 1) old)) := by
  apply and_intro ?_ .rfl
  iintro ⟨Ha, Hcell⟩
  isimp only [pointsTo] at Hcell
  iapply ghost_map_lookup $$ Ha Hcell

/-- A store under any mask containing the invariant namespace. The two
state events agree with the invariant's half before its update and closure. -/
theorem wpiMask_store'_subset (N : Namespace) (γ : GName) (mask : CoPset)
    (hmask : (↑N : CoPset) ⊆ mask) (location : Nat)
    (old next : Option V) (Φ : Option V → IProp GF) :
    iprop(pointsTo γ location (.own 1) old ∗
      (pointsTo γ location (.own 1) next -∗ Φ old)) ⊢
      wpiMask (heapH (V := V) N γ) mask (store' location next) Φ := by
  iintro ⟨Hcell, Hcont⟩
  unfold wpiMask
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hrestore
  rw [store', getState, trigger, ITree.bind_vis, wpi_vis]
  imodintro
  isimp only [heapH, stateH, stateHandle]
  iintro %heap Hstate
  isimp only [heapStateInterp, StateInterp.interp, heapState_as_half, heapInv_as_half] at Hstate
  icases persistent_and_sep_mp $$ Hstate with ⟨HstateAuth, #Hinv⟩
  imod Hrestore
  imod inv_acc_timeless (E := mask) (N := N) hmask $$ Hinv with
    ⟨HinvAuth, Hclose⟩
  · iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro HrestoreMiddle
    icases HinvAuth with ⟨%other, Hother⟩
    ihave ⟨%heq, HstateAuth, Hother⟩ := halves_agree γ heap other $$ [$HstateAuth $Hother]
    subst other
    ihave ⟨%hlookup, HstateAuth, Hcell⟩ :=
      half_lookup γ heap location old $$ [$HstateAuth $Hcell]
    ihave Hstate := state_from_half N γ heap $$ [$HstateAuth $Hinv]
    isplitl [Hstate]
    · iframe Hstate
    · rw [ITree.bind_ret, setState, trigger, ITree.bind_vis, wpi_vis]
      imodintro
      isimp only [heapH, stateH, stateHandle]
      iintro %seen Hseen
      isimp only [heapStateInterp, StateInterp.interp, heapState_as_half,
        heapInv_as_half] at Hseen
      icases persistent_and_sep_mp $$ Hseen with ⟨HseenAuth, #HinvSeen⟩
      ihave ⟨%heqSeen, HseenAuth, Hother⟩ :=
        halves_agree γ seen heap $$ [$HseenAuth $Hother]
      subst seen
      imod two_halves_update_explicit γ heap location old next $$
        [$HseenAuth $Hother $Hcell] with ⟨HnextAuth, HotherNext, Hcell⟩
      imodintro
      ihave HnextState :=
        state_from_half N γ (Iris.Std.insert (M := HeapMap) heap location next) $$
          [$HnextAuth $Hinv]
      isplitl [HnextState]
      · iframe HnextState
      · rw [hlookup, Option.join_some, ITree.bind_ret, wpi_ret]
        imodintro
        imod HrestoreMiddle
        imod Hclose $$ [HotherNext]
        · iexists (Iris.Std.insert (M := HeapMap) heap location next)
          iexact HotherNext
        · imodintro
          iapply Hcont $$ Hcell

/-- Backwards-compatible namespace-mask specialization. -/
theorem wpiMask_store' (N : Namespace) (γ : GName) (location : Nat)
    (old next : Option V) (Φ : Option V → IProp GF) :
    iprop(pointsTo γ location (.own 1) old ∗
      (pointsTo γ location (.own 1) next -∗ Φ old)) ⊢
      wpiMask (heapH (V := V) N γ) (↑N) (store' location next) Φ :=
  wpiMask_store'_subset N γ (↑N) (fun _ h => h) location old next Φ

/-- Masked store specification for a present cell, including a freed cell. -/
theorem wpiMask_store'_spec (N : Namespace) (γ : GName) (location : Nat)
    (old next : Option V) :
    pointsTo (V := V) (GF := GF) γ location (.own 1) old ⊢
      wpiMask (heapH (V := V) N γ) (↑N) (store' location next)
        (fun result => iprop(⌜result = old⌝ ∗ pointsTo γ location (.own 1) next)) := by
  iintro Hcell
  iapply wpiMask_store' N γ location old next
  iframe Hcell
  iintro Hcell
  iframe Hcell
  itrivial

/-- Specialization to a write of a concrete value. -/
theorem wpiMask_store (N : Namespace) (γ : GName) (location : Nat)
    (old : Option V) (next : V) (Φ : Option V → IProp GF) :
    iprop(pointsTo γ location (.own 1) old ∗
      (pointsTo γ location (.own 1) (some next) -∗ Φ old)) ⊢
      wpiMask (heapH (V := V) N γ) (↑N) (store location next) Φ :=
  wpiMask_store' N γ location old (some next) Φ

/-- Store specification under any mask containing the heap invariant. -/
theorem wpiMask_store'_spec_subset (N : Namespace) (γ : GName)
    (mask : CoPset) (hmask : (↑N : CoPset) ⊆ mask)
    (location : Nat) (old next : Option V) :
    pointsTo (V := V) (GF := GF) γ location (.own 1) old ⊢
      wpiMask (heapH (V := V) N γ) mask (store' location next)
        (fun result => iprop(⌜result = old⌝ ∗ pointsTo γ location (.own 1) next)) := by
  iintro Hcell
  iapply wpiMask_store'_subset N γ mask hmask location old next
  iframe Hcell
  iintro Hcell
  iframe Hcell
  itrivial

/-- Write a concrete value under an arbitrary admissible mask. -/
theorem wpiMask_store_subset (N : Namespace) (γ : GName)
    (mask : CoPset) (hmask : (↑N : CoPset) ⊆ mask)
    (location : Nat) (old : Option V) (next : V) (Φ : Option V → IProp GF) :
    iprop(pointsTo γ location (.own 1) old ∗
      (pointsTo γ location (.own 1) (some next) -∗ Φ old)) ⊢
      wpiMask (heapH (V := V) N γ) mask (store location next) Φ :=
  wpiMask_store'_subset N γ mask hmask location old (some next) Φ

/-- Freeing preserves a present map key with value `none`. -/
theorem wpiMask_free_subset (N : Namespace) (γ : GName)
    (mask : CoPset) (hmask : (↑N : CoPset) ⊆ mask)
    (location : Nat) (old : Option V) (Φ : Option V → IProp GF) :
    iprop(pointsTo γ location (.own 1) old ∗
      (pointsTo γ location (.own 1) (none : Option V) -∗ Φ old)) ⊢
      wpiMask (heapH (V := V) N γ) mask (free (V := V) location) Φ :=
  wpiMask_store'_subset N γ mask hmask location old none Φ

theorem wpiMask_free_spec_subset (N : Namespace) (γ : GName)
    (mask : CoPset) (hmask : (↑N : CoPset) ⊆ mask)
    (location : Nat) (old : Option V) :
    pointsTo (V := V) (GF := GF) γ location (.own 1) old ⊢
      wpiMask (heapH (V := V) N γ) mask (free (V := V) location)
        (fun result => iprop(⌜result = old⌝ ∗ pointsTo γ location (.own 1) (none : Option V))) := by
  iintro Hcell
  iapply wpiMask_free_subset N γ mask hmask location old
  iframe Hcell
  iintro Hcell
  iframe Hcell
  itrivial

/-- Namespace-mask specialization of the free rule. -/
theorem wpiMask_free (N : Namespace) (γ : GName) (location : Nat)
    (old : Option V) (Φ : Option V → IProp GF) :
    iprop(pointsTo γ location (.own 1) old ∗
      (pointsTo γ location (.own 1) (none : Option V) -∗ Φ old)) ⊢
      wpiMask (heapH (V := V) N γ) (↑N) (free (V := V) location) Φ :=
  wpiMask_free_subset N γ (↑N) (fun _ h => h) location old Φ

theorem wpiMask_free_spec (N : Namespace) (γ : GName) (location : Nat)
    (old : Option V) :
    pointsTo (V := V) (GF := GF) γ location (.own 1) old ⊢
      wpiMask (heapH (V := V) N γ) (↑N) (free (V := V) location)
        (fun result => iprop(⌜result = old⌝ ∗ pointsTo γ location (.own 1) (none : Option V))) :=
  wpiMask_free_spec_subset N γ (↑N) (fun _ h => h) location old

end Rules

end ProgramLogicCarte.HeapLogic
