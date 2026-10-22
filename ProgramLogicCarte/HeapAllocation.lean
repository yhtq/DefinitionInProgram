import ProgramLogicCarte.HeapOperations

/-! Allocation in the finite-map heap. Missing keys are unallocated, including
when another key contains the freed-cell value `none`. -/

namespace ProgramLogicCarte.HeapLogic

open Iris Iris.BI ITree Iris.Std Iris.Std.PartialMap

/-- Choose a key outside the finite heap. -/
noncomputable def fresh {V : Type} (heap : Heap V) : Nat :=
  letI := Classical.instUnboundedHeapCompare (K := Nat)
  Iris.Std.fresh (M := HeapMap) (m := heap) trivial

@[simp] theorem lookup_fresh {V : Type} (heap : Heap V) :
    get? (M := HeapMap) heap (fresh heap) = none := by
  let _ := Classical.instUnboundedHeapCompare (K := Nat)
  exact Iris.Std.get?_fresh (M := HeapMap)

/-- Allocate one fresh location. This is the single-cell specialization of
upstream `allocN 1`; no contiguous-block claim is made about `fresh`. -/
noncomputable def alloc {V : Type} (value : V) : ITree (HeapE V) Nat :=
  (getState (fun e => e)).bind fun heap =>
    (setState (fun e => e)
      (Iris.Std.insert (M := HeapMap) heap (fresh heap) (some value))).bind fun _ =>
      ret (fresh heap)

section Rules

variable {V : Type} {GF : BundledGFunctors} {hlc : HasLC}
variable [InvGS_gen hlc GF] [GhostMapG GF Nat (Option V) HeapMap]

private def allocHalf : DFrac := .own ((1 : Qp).half)

/-- Recombine the handler and invariant halves to allocate a full cell, then
split the updated authority again. -/
theorem two_halves_insert (γ : GName) (heap : Heap V) (location : Nat)
    (value : Option V) (hfree : get? (M := HeapMap) heap location = none) :
    iprop(ghost_map_auth (GF := GF) (H := HeapMap) γ allocHalf heap ∗
      ghost_map_auth (H := HeapMap) γ allocHalf heap) ⊢
    iprop(|={∅}=> ghost_map_auth (H := HeapMap) γ allocHalf
        (Iris.Std.insert (M := HeapMap) heap location value) ∗
      ghost_map_auth (H := HeapMap) γ allocHalf
        (Iris.Std.insert (M := HeapMap) heap location value) ∗
      pointsTo γ location (.own 1) value) := by
  have hsplit (m : Heap V) :
      (ghost_map_auth (H := HeapMap) γ (.own (1 : Qp)) m : IProp GF) ⊣⊢
        iprop(ghost_map_auth (H := HeapMap) γ allocHalf m ∗
          ghost_map_auth (H := HeapMap) γ allocHalf m) := by
    simpa only [allocHalf, Qp.half_add_half] using
      (Fractional.fractional (PROP := IProp GF)
        (Φ := fun q => ghost_map_auth (H := HeapMap) γ (.own q) m)
        (1 : Qp).half (1 : Qp).half)
  iintro ⟨Ha, Hb⟩
  ihave Hauth := (hsplit heap).mpr $$ [$Ha $Hb]
  imod ghost_map_insert location value hfree $$ Hauth with ⟨Hauth, Hcell⟩
  imodintro
  icases (hsplit (Iris.Std.insert (M := HeapMap) heap location value)).mp $$ Hauth with
    ⟨Ha, Hb⟩
  isimp only [pointsTo]
  iframe

private theorem alloc_state_eq (N : Namespace) (γ : GName) (heap : Heap V) :
    heapState (V := V) (GF := GF) N γ heap =
      iprop(ghost_map_auth (H := HeapMap) γ allocHalf heap ∧ heapInv (V := V) N γ) := by
  rfl

private theorem alloc_inv_eq (N : Namespace) (γ : GName) :
    heapInv (V := V) (GF := GF) N γ =
      inv N (iprop(∃ heap : Heap V, ghost_map_auth (H := HeapMap) γ allocHalf heap)) := by
  rfl

private theorem alloc_halves_agree (γ : GName) (left right : Heap V) :
    iprop(ghost_map_auth (GF := GF) (H := HeapMap) γ allocHalf left ∗
      ghost_map_auth (H := HeapMap) γ allocHalf right) ⊢
    iprop(⌜left = right⌝ ∧
      (ghost_map_auth (H := HeapMap) γ allocHalf left ∗
       ghost_map_auth (H := HeapMap) γ allocHalf right)) := by
  apply and_intro ?_ .rfl
  iintro ⟨Ha, Hb⟩
  iapply ghost_map_auth_agree (H := HeapMap) $$ Ha Hb

/-- Allocate a fresh cell while temporarily opening the heap invariant. -/
theorem wpiMask_alloc (N : Namespace) (γ : GName) (mask : CoPset)
    (hmask : (↑N : CoPset) ⊆ mask) (value : V) (Φ : Nat → IProp GF) :
    iprop(∀ location : Nat, pointsTo γ location (.own 1) (some value) -∗ Φ location) ⊢
      wpiMask (heapH (V := V) N γ) mask (alloc value) Φ := by
  iintro Hcont
  unfold wpiMask
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hrestore
  rw [alloc, getState, trigger, ITree.bind_vis, wpi_vis]
  imodintro
  isimp only [heapH, stateH, stateHandle]
  iintro %heap Hstate
  isimp only [heapStateInterp, StateInterp.interp, alloc_state_eq, alloc_inv_eq] at Hstate
  icases persistent_and_sep_mp $$ Hstate with ⟨HstateAuth, #Hinv⟩
  imod Hrestore
  imod inv_acc_timeless (E := mask) (N := N) hmask $$ Hinv with ⟨Hopened, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro HrestoreInner
  icases Hopened with ⟨%current, HinvHalf⟩
  ihave ⟨%heq, HstateAuth, HinvHalf⟩ :=
    alloc_halves_agree γ heap current $$ [$HstateAuth $HinvHalf]
  subst current
  isplitl [HstateAuth]
  · isimp only [heapStateInterp, StateInterp.interp, alloc_state_eq, alloc_inv_eq]
    isplit
    · iexact HstateAuth
    · iexact Hinv
  · rw [ITree.bind_ret, setState, trigger, ITree.bind_vis, wpi_vis]
    imodintro
    isimp only [heapH, stateH, stateHandle]
    iintro %before Hbefore
    isimp only [heapStateInterp, StateInterp.interp, alloc_state_eq, alloc_inv_eq] at Hbefore
    icases persistent_and_sep_mp $$ Hbefore with ⟨HbeforeHalf, #HinvBefore⟩
    ihave ⟨%heq, HbeforeHalf, HinvHalf⟩ :=
      alloc_halves_agree γ before heap $$ [$HbeforeHalf $HinvHalf]
    subst before
    imod two_halves_insert γ heap (fresh heap) (some value) (lookup_fresh heap)
      $$ [$HbeforeHalf $HinvHalf] with ⟨Hnext, HinvNext, Hcell⟩
    imodintro
    isimp only [heapStateInterp, StateInterp.interp, alloc_state_eq, alloc_inv_eq]
    isplitl [Hnext]
    · isplit
      · iexact Hnext
      · iexact HinvBefore
    · rw [ITree.bind_ret, wpi_ret]
      imodintro
      imod HrestoreInner
      ihave Hexists := (show
          (ghost_map_auth (GF := GF) (H := HeapMap) γ allocHalf
            (Iris.Std.insert (M := HeapMap) heap (fresh heap) (some value)) : IProp GF) ⊢
          iprop(∃ current : Heap V, ghost_map_auth (H := HeapMap) γ allocHalf current) from by
            iintro Ha
            iexists (Iris.Std.insert (M := HeapMap) heap (fresh heap) (some value))
            iexact Ha) $$ HinvNext
      imod Hclose $$ Hexists
      imodintro
      iapply Hcont $$ %(fresh heap) Hcell

/-- A single allocation returns full ownership of the newly created cell. -/
theorem wpiMask_alloc_spec (N : Namespace) (γ : GName) (mask : CoPset)
    (hmask : (↑N : CoPset) ⊆ mask) (value : V) :
    ⊢ wpiMask (heapH (V := V) (GF := GF) N γ) mask (alloc value)
      (fun location => pointsTo γ location (.own 1) (some value)) := by
  iapply wpiMask_alloc N γ mask hmask value
  iintro %location Hcell
  iexact Hcell

/-- The allocated cell's ownership establishes the WP for a subsequent read.
This is a nested specification, not a bind rule for `wpiMask`. -/
theorem wpiMask_alloc_then_load (N : Namespace) (γ : GName) (mask : CoPset)
    (hmask : (↑N : CoPset) ⊆ mask) (value : V) :
    ⊢ wpiMask (heapH (V := V) (GF := GF) N γ) mask (alloc value)
      (fun location => wpiMask (heapH N γ) mask (load location)
        (fun result => iprop(⌜result = some value⌝ ∗
          pointsTo γ location (.own 1) (some value)))) := by
  iapply wpiMask_alloc N γ mask hmask value
  iintro %location Hcell
  iapply wpiMask_load_spec N γ mask location (.own 1) (some value)
  iexact Hcell

end Rules

end ProgramLogicCarte.HeapLogic
