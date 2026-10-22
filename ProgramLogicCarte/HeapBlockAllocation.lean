import ProgramLogicCarte.HeapAllocation

/-! Contiguous fresh blocks in the finite-map heap. A missing key is free;
 a present key holding `none` is not. -/

namespace ProgramLogicCarte.HeapLogic

open Iris Iris.BI ITree Iris.Std Iris.Std.PartialMap

/-- An upper bound on the occupied locations, computed from the finite map. -/
private def blockStart {V : Type} (heap : Heap V) : Nat :=
  (heap.toList.map Prod.fst).foldl max 0 + 1

private theorem fold_max_ge (xs : List Nat) (a : Nat) :
    a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact (Nat.le_max_left a x).trans (ih (max a x))

private theorem le_foldl_max (xs : List Nat) (a k : Nat) (hk : k ∈ xs) :
    k ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => cases hk
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hk with rfl | hk
    · exact (Nat.le_max_right a k).trans (fold_max_ge xs (max a k))
    · exact ih (max a x) hk

/-- Every cell in the chosen interval is absent, even for an empty block. -/
theorem blockStart_fresh {V : Type} (heap : Heap V) (i : Nat) :
    get? (M := HeapMap) heap (blockStart heap + i) = none := by
  classical
  by_contra h
  obtain ⟨v, hv⟩ : ∃ v, get? (M := HeapMap) heap (blockStart heap + i) = some v := by
    cases hlookup : get? (M := HeapMap) heap (blockStart heap + i) with
    | none => exact False.elim (h hlookup)
    | some v => exact ⟨v, rfl⟩
  have hm : blockStart heap + i ∈ heap.toList.map Prod.fst :=
    List.mem_map_of_mem (LawfulFiniteMap.toList_get.mpr hv)
  have hb := le_foldl_max (heap.toList.map Prod.fst) 0 (blockStart heap + i) hm
  unfold blockStart at hb
  omega

/-- The block is a finite map of exactly `n` consecutive occupied keys. -/
def blockMap {V : Type} (start n : Nat) (value : V) : Heap V :=
  FiniteMap.map_seq (M := HeapMap) start (List.replicate n (some value))

/-- The newly constructed block never overlaps the existing heap. -/
theorem blockMap_disjoint {V : Type} (heap : Heap V) (n : Nat) (value : V) :
    PartialMap.disjoint (M := HeapMap) (blockMap (blockStart heap) n value) heap := by
  rw [PartialMap.disjoint_iff]
  intro k
  by_cases h : blockStart heap ≤ k
  · by_cases hr : k - blockStart heap < n
    · right
      have heq : k = blockStart heap + (k - blockStart heap) := by omega
      rw [heq]
      exact blockStart_fresh heap _
    · left
      rw [blockMap, LawfulFiniteMap.get?_map_seq, ite_eq_left h]
      have hn : (List.replicate n (some value)).length ≤ k - blockStart heap := by
        simp only [List.length_replicate]
        omega
      exact List.getElem?_eq_none hn
  · left
    rw [blockMap, LawfulFiniteMap.get?_map_seq, ite_eq_right h]

/-- The upstream `allocN` state transition, with a deterministic fresh block. -/
noncomputable def allocN {V : Type} (n : Nat) (value : V) : ITree (HeapE V) Nat :=
  (getState (fun e => e)).bind fun heap =>
    (setState (fun e => e)
      (PartialMap.union (M := HeapMap) (blockMap (blockStart heap) n value) heap)).bind fun _ =>
        ret (blockStart heap)

section Rules

variable {V : Type} {GF : BundledGFunctors} {hlc : HasLC}
variable [InvGS_gen hlc GF] [GhostMapG GF Nat (Option V) HeapMap]

private def blockHalf : DFrac := .own ((1 : Qp).half)

/-- Insert a disjoint contiguous block using the two authority halves. -/
theorem two_halves_insert_big (γ : GName) (heap : Heap V) (n : Nat) (value : V) :
    iprop(ghost_map_auth (GF := GF) (H := HeapMap) γ blockHalf heap ∗
      ghost_map_auth (H := HeapMap) γ blockHalf heap) ⊢
    iprop(|={∅}=> ghost_map_auth (H := HeapMap) γ blockHalf
        (PartialMap.union (M := HeapMap) (blockMap (blockStart heap) n value) heap) ∗
      ghost_map_auth (H := HeapMap) γ blockHalf
        (PartialMap.union (M := HeapMap) (blockMap (blockStart heap) n value) heap) ∗
      Iris.BI.bigSepM (M := HeapMap)
        (fun location cell => pointsTo (V := V) γ location (.own 1) cell)
        (blockMap (blockStart heap) n value)) := by
  have hsplit (m : Heap V) :
      (ghost_map_auth (H := HeapMap) γ (.own (1 : Qp)) m : IProp GF) ⊣⊢
        iprop(ghost_map_auth (H := HeapMap) γ blockHalf m ∗
          ghost_map_auth (H := HeapMap) γ blockHalf m) := by
    simpa only [blockHalf, Qp.half_add_half] using
      (Fractional.fractional (PROP := IProp GF)
        (Φ := fun q => ghost_map_auth (H := HeapMap) γ (.own q) m)
        (1 : Qp).half (1 : Qp).half)
  iintro ⟨Ha, Hb⟩
  ihave Hauth := (hsplit heap).mpr $$ [$Ha $Hb]
  imod ghost_map_insert_big (H := HeapMap) (blockMap (blockStart heap) n value)
    (blockMap_disjoint heap n value) $$ Hauth with ⟨Hauth, Hcells⟩
  imodintro
  icases (hsplit (PartialMap.union (M := HeapMap)
    (blockMap (blockStart heap) n value) heap)).mp $$ Hauth with
    ⟨Ha, Hb⟩
  isimp only [pointsTo]
  iframe

private theorem block_state_eq (N : Namespace) (γ : GName) (heap : Heap V) :
    heapState (V := V) (GF := GF) N γ heap =
      iprop(ghost_map_auth (H := HeapMap) γ blockHalf heap ∧ heapInv (V := V) N γ) := by
  rfl

private theorem block_inv_eq (N : Namespace) (γ : GName) :
    heapInv (V := V) (GF := GF) N γ =
      inv N (iprop(∃ heap : Heap V, ghost_map_auth (H := HeapMap) γ blockHalf heap)) := by
  rfl

private theorem block_halves_agree (γ : GName) (left right : Heap V) :
    iprop(ghost_map_auth (GF := GF) (H := HeapMap) γ blockHalf left ∗
      ghost_map_auth (H := HeapMap) γ blockHalf right) ⊢
    iprop(⌜left = right⌝ ∧
      (ghost_map_auth (H := HeapMap) γ blockHalf left ∗
       ghost_map_auth (H := HeapMap) γ blockHalf right)) := by
  apply and_intro ?_ .rfl
  iintro ⟨Ha, Hb⟩
  iapply ghost_map_auth_agree (H := HeapMap) $$ Ha Hb

/-- Allocate a contiguous block while opening the heap invariant only within the mask. -/
theorem wpiMask_allocN (N : Namespace) (γ : GName) (mask : CoPset)
    (hmask : (↑N : CoPset) ⊆ mask) (n : Nat) (value : V) (Φ : Nat → IProp GF) :
    iprop(∀ start : Nat,
      Iris.BI.bigSepM (M := HeapMap)
        (fun location cell => pointsTo (V := V) γ location (.own 1) cell)
        (blockMap start n value) -∗ Φ start) ⊢
      wpiMask (heapH (V := V) N γ) mask (allocN n value) Φ := by
  iintro Hcont
  unfold wpiMask
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hrestore
  rw [allocN, getState, trigger, ITree.bind_vis, wpi_vis]
  imodintro
  isimp only [heapH, stateH, stateHandle]
  iintro %heap Hstate
  isimp only [heapStateInterp, StateInterp.interp, block_state_eq, block_inv_eq] at Hstate
  icases persistent_and_sep_mp $$ Hstate with ⟨HstateAuth, #Hinv⟩
  imod Hrestore
  imod inv_acc_timeless (E := mask) (N := N) hmask $$ Hinv with ⟨Hopened, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro HrestoreInner
  icases Hopened with ⟨%current, HinvHalf⟩
  ihave ⟨%heq, HstateAuth, HinvHalf⟩ :=
    block_halves_agree γ heap current $$ [$HstateAuth $HinvHalf]
  subst current
  isplitl [HstateAuth]
  · isimp only [heapStateInterp, StateInterp.interp, block_state_eq, block_inv_eq]
    isplit
    · iexact HstateAuth
    · iexact Hinv
  · rw [ITree.bind_ret, setState, trigger, ITree.bind_vis, wpi_vis]
    imodintro
    isimp only [heapH, stateH, stateHandle]
    iintro %before Hbefore
    isimp only [heapStateInterp, StateInterp.interp, block_state_eq, block_inv_eq] at Hbefore
    icases persistent_and_sep_mp $$ Hbefore with ⟨HbeforeHalf, #HinvBefore⟩
    ihave ⟨%heq, HbeforeHalf, HinvHalf⟩ :=
      block_halves_agree γ before heap $$ [$HbeforeHalf $HinvHalf]
    subst before
    imod two_halves_insert_big γ heap n value
      $$ [$HbeforeHalf $HinvHalf] with ⟨Hnext, HinvNext, Hcells⟩
    imodintro
    isimp only [heapStateInterp, StateInterp.interp, block_state_eq, block_inv_eq]
    isplitl [Hnext]
    · isplit
      · iexact Hnext
      · iexact HinvBefore
    · rw [ITree.bind_ret, wpi_ret]
      imodintro
      imod HrestoreInner
      ihave Hexists := (show
          (ghost_map_auth (GF := GF) (H := HeapMap) γ blockHalf
            (PartialMap.union (M := HeapMap)
              (blockMap (blockStart heap) n value) heap) : IProp GF) ⊢
          iprop(∃ current : Heap V, ghost_map_auth (H := HeapMap) γ blockHalf current) from by
            iintro Ha
            iexists (PartialMap.union (M := HeapMap)
              (blockMap (blockStart heap) n value) heap)
            iexact Ha) $$ HinvNext
      imod Hclose $$ Hexists
      imodintro
      iapply Hcont $$ %(blockStart heap) Hcells

/-- List-indexed presentation of the full fragments at `start + i`,
matching the upstream contiguous-array postcondition. -/
theorem wpiMask_allocN_list (N : Namespace) (γ : GName) (mask : CoPset)
    (hmask : (↑N : CoPset) ⊆ mask) (n : Nat) (value : V) (Φ : Nat → IProp GF) :
    iprop(∀ start : Nat,
      Iris.BI.bigSepL
        (fun i _ => pointsTo (V := V) γ (start + i) (.own 1) (some value))
        (List.replicate n value) -∗ Φ start) ⊢
      wpiMask (heapH (V := V) N γ) mask (allocN n value) Φ := by
  iintro Hcont
  iapply wpiMask_allocN N γ mask hmask n value
  iintro %start Hcells
  iapply Hcont $$ %start
  have hmap := (Iris.BI.BigSepM.bigSepM_map_seq (PROP := IProp GF) (M' := HeapMap)
    (Φ := fun location cell => pointsTo (V := V) γ location (.own 1) cell)
    (start := start) (l := List.replicate n (some value))).mp
  isimp only [blockMap] at Hcells
  ihave Hlist := hmap $$ Hcells
  isimp only [← List.map_replicate, Iris.BI.BigSepL.bigSepL_map] at Hlist
  have heq : ∀ {k x}, (List.replicate n value)[k]? = some x →
      pointsTo (GF := GF) γ (start + k) (.own 1) (some x) =
        pointsTo γ (start + k) (.own 1) (some value) := by
    intro k x hx
    have hv : x = value := List.eq_of_mem_replicate (List.mem_of_getElem? hx)
    rw [hv]
  isimp only [Iris.BI.BigSepL.bigSepL_eq heq] at Hlist
  iexact Hlist

end Rules

end ProgramLogicCarte.HeapLogic
