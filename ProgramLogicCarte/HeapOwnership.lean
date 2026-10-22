import ProgramLogicCarte.StateOwnership
import Iris.BI.Lib.GenHeap

/-!
# An authoritative finite heap for the ownership-taking logical handler

The state is a finite map from natural locations to optional values. A missing
key is unallocated; a present `none` is a freed cell. The resource model is
Iris's `genHeap`, with its standard fractional points-to assertions.

`interp` owns the heap authority. `wp` hands that authority to
`ownershipStateH` and requires it back in the postcondition. Consequently the
client rules have ordinary points-to preconditions, and genuine writes update
authority and cell ownership together. Authority is passed, not framed as an
unchanging resource. This is not an instance of the separate, framed-authority
interface in `StateOwnershipAdequacy`.
-/

namespace ProgramLogicCarte.OwnershipHeap

open Iris Iris.BI ITree Iris.Std Iris.Std.PartialMap

abbrev HeapMap := fun V : Type => Std.ExtTreeMap Nat V compare
abbrev Heap (V : Type) := HeapMap (Option V)

/-- Absent and freed cells both read as `none`, but have different lookups. -/
def load {V : Type} (location : Nat) : ITree (StateE (Heap V)) (Option V) :=
  (getState (fun e => e)).bind fun heap => ret ((get? (M := HeapMap) heap location).join)

/-- Return the previous value and replace the cell. -/
def store' {V : Type} (location : Nat) (value : Option V) :
    ITree (StateE (Heap V)) (Option V) :=
  (getState (fun e => e)).bind fun heap =>
    (setState (fun e => e) (Iris.Std.insert (M := HeapMap) heap location value)).bind fun _ =>
      ret ((get? (M := HeapMap) heap location).join)

def store {V : Type} (location : Nat) (value : V) :
    ITree (StateE (Heap V)) (Option V) := store' location (some value)

/-- Freeing retains an allocated, empty cell, as in the existing heap effects. -/
def free {V : Type} (location : Nat) : ITree (StateE (Heap V)) (Option V) :=
  store' location none

/-- Choose a location outside the finite heap. -/
noncomputable def fresh {V : Type} (heap : Heap V) : Nat :=
  letI := Classical.instUnboundedHeapCompare (K := Nat)
  Iris.Std.fresh (M := HeapMap) (m := heap) trivial

theorem lookup_fresh {V : Type} (heap : Heap V) : get? (M := HeapMap) heap (fresh heap) = none := by
  let _ := Classical.instUnboundedHeapCompare (K := Nat)
  exact Iris.Std.get?_fresh (M := HeapMap)

noncomputable def alloc {V : Type} (value : V) : ITree (StateE (Heap V)) Nat :=
  (getState (fun e => e)).bind fun heap =>
    (setState (fun e => e) (Iris.Std.insert (M := HeapMap) heap (fresh heap) (some value))).bind fun _ =>
      ret (fresh heap)

section Logic

variable {V : Type} {GF : BundledGFunctors} {hlc : HasLC}
variable [InvGS_gen hlc GF] [G : genHeapGS Nat (Option V) GF HeapMap]

def authority (heap : Heap V) : IProp GF := genHeapInterp heap

instance heapStateInterp : StateInterp (IProp GF) (Heap V) where
  interp := authority

def handler : IHandlerBase (IProp GF) (StateE (Heap V)) := ownershipStateH (Heap V)

private theorem handler_get (Φ spawned : Heap V → IProp GF) :
    (handler (V := V)).handle StateE.get Φ spawned =
      iprop(∃ heap : Heap V, authority heap ∗ (authority heap -∗ Φ heap)) := rfl

private theorem handler_set (next : Heap V) (Φ spawned : ULift Unit → IProp GF) :
    (handler (V := V)).handle (StateE.set next) Φ spawned =
      iprop(∃ heap : Heap V, authority heap ∗
        (authority heap -∗ |={∅}=> authority next ∗ (authority next -∗ Φ (.up ())))) := rfl

/-- Full or fractional ownership of one cell; `none` describes a freed cell. -/
def cell (location : Nat) (fraction : DFrac) (value : Option V) : IProp GF :=
  pointsTo location fraction value

/-- Supply runtime authority to the logical handler and recover final authority.
The client owns the cells it uses; it does not have to own the entire heap. -/
def wp {ρ : Type} (t : ITree (StateE (Heap V)) ρ) (Φ : ρ → IProp GF) : IProp GF :=
  iprop(∀ heap : Heap V, authority heap -∗
    wpi handler t (fun r => iprop(∃ final : Heap V, authority final ∗ Φ r)))

/-- The client-facing WP is a specification of the actual logical handler. -/
theorem wp_apply {ρ : Type} (heap : Heap V) (t : ITree (StateE (Heap V)) ρ)
    (Φ : ρ → IProp GF) :
    iprop(authority heap ∗ wp t Φ) ⊢
      wpi handler t (fun r => iprop(∃ final : Heap V, authority final ∗ Φ r)) := by
  iintro ⟨Hheap, Hwp⟩
  isimp only [wp] at Hwp
  iapply Hwp $$ %heap Hheap

/-- Agreement preserves both authority and the fractional cell token. -/
theorem authority_cell_agree (heap : Heap V) (location : Nat)
    (fraction : DFrac) (value : Option V) :
    iprop(authority (GF := GF) heap ∗ cell location fraction value) ⊢
    iprop(⌜get? (M := HeapMap) heap location = some value⌝ ∧
      (authority heap ∗ cell location fraction value)) := by
  apply and_intro ?_ .rfl
  unfold authority cell genHeapInterp pointsTo
  iintro ⟨⟨%m, _, Hheap, _⟩, Hcell⟩
  iapply ghost_map_lookup $$ Hheap Hcell

/-- A full cell token cannot be duplicated, even with a different value. -/
theorem cell_exclusive (location : Nat) (v₁ v₂ : Option V) :
    iprop(cell (GF := GF) location (.own 1) v₁ ∗ cell location (.own 1) v₂) ⊢
      iprop(False) := by
  unfold cell
  iintro H
  ihave ⟨%hvalid, _⟩ := pointsTo_op_cmraValid $$ H
  exact (DFrac.own_whole_exclusive.exclusive0_l _ hvalid.validN).elim

/-- A concrete store updates heap authority and cell ownership together. -/
theorem authority_cell_update (heap : Heap V) (location : Nat)
    (old next : Option V) :
    iprop(authority (GF := GF) heap ∗ cell location (.own 1) old) ⊢
      iprop(|={∅}=> authority (Iris.Std.insert (M := HeapMap) heap location next) ∗ cell location (.own 1) next) := by
  unfold authority cell
  iintro H
  imod genHeap_update $$ H with H
  imodintro
  iexact H

theorem wp_ret {ρ : Type} (r : ρ) (Φ : ρ → IProp GF) :
    Φ r ⊢ wp (V := V) (ret r) Φ := by
  iintro Hpost
  unfold wp
  iintro %heap Hheap
  rw [wpi_ret]
  imodintro
  iexists heap
  iframe

/-- Read rule in continuation form. Any valid fractional cell ownership suffices. -/
theorem wp_load_bind {ρ : Type} (location : Nat) (fraction : DFrac)
    (value : Option V) (k : Option V → ITree (StateE (Heap V)) ρ)
    (Φ : ρ → IProp GF) :
    iprop(cell (GF := GF) location fraction value ∗
      (cell location fraction value -∗ wp (k value) Φ)) ⊢
    wp (load location |>.bind k) Φ := by
  iintro ⟨Hcell, Hcont⟩
  unfold wp
  iintro %heap Hheap
  rw [load, getState, trigger, ITree.bind_vis, ITree.bind_vis, wpi_vis]
  imodintro
  isimp only [handler_get]
  iexists heap
  iframe Hheap
  iintro Hheap
  ihave ⟨%hlookup, Hheap, Hcell⟩ := authority_cell_agree heap location fraction value $$ [$Hheap $Hcell]
  rw [ITree.bind_ret, ITree.bind_ret, hlookup, Option.join_some]
  ispecialize Hcont $$ Hcell
  ispecialize Hcont $$ %heap Hheap
  iexact Hcont

/-- Write rule in continuation form. The continuation receives the updated cell. -/
theorem wp_store'_bind {ρ : Type} (location : Nat) (old next : Option V)
    (k : Option V → ITree (StateE (Heap V)) ρ) (Φ : ρ → IProp GF) :
    iprop(cell (GF := GF) location (.own 1) old ∗
      (cell location (.own 1) next -∗ wp (k old) Φ)) ⊢
    wp (store' location next |>.bind k) Φ := by
  iintro ⟨Hcell, Hcont⟩
  unfold wp
  iintro %heap Hheap
  rw [store', getState, trigger, ITree.bind_vis, ITree.bind_vis, wpi_vis]
  imodintro
  isimp only [handler_get]
  iexists heap
  iframe Hheap
  iintro Hheap
  ihave ⟨%hlookup, Hheap, Hcell⟩ := authority_cell_agree heap location (.own 1) old $$ [$Hheap $Hcell]
  rw [ITree.bind_ret, setState, trigger, ITree.bind_vis, ITree.bind_vis, wpi_vis]
  imodintro
  isimp only [handler_set]
  iexists heap
  iframe Hheap
  iintro Hheap
  imod authority_cell_update heap location old next $$ [$Hheap $Hcell] with ⟨Hheap, Hcell⟩
  imodintro
  iframe Hheap
  iintro Hheap
  rw [ITree.bind_ret, ITree.bind_ret, hlookup, Option.join_some]
  ispecialize Hcont $$ Hcell
  ispecialize Hcont $$ %(Iris.Std.insert (M := HeapMap) heap location next) Hheap
  iexact Hcont

/-- Allocation needs no cell ownership and returns full ownership of a fresh cell. -/
theorem wp_alloc_bind {ρ : Type} (value : V)
    (k : Nat → ITree (StateE (Heap V)) ρ) (Φ : ρ → IProp GF) :
    iprop(∀ location : Nat, cell (GF := GF) location (.own 1) (some value) -∗ wp (k location) Φ) ⊢
    wp (alloc value |>.bind k) Φ := by
  iintro Hcont
  unfold wp
  iintro %heap Hheap
  rw [alloc, getState, trigger, ITree.bind_vis, ITree.bind_vis, wpi_vis]
  imodintro
  isimp only [handler_get]
  iexists heap
  iframe Hheap
  iintro Hheap
  rw [ITree.bind_ret, setState, trigger, ITree.bind_vis, ITree.bind_vis, wpi_vis]
  imodintro
  isimp only [handler_set]
  iexists heap
  iframe Hheap
  iintro Hheap
  unfold authority at *
  imod genHeap_alloc (lookup_fresh heap) $$ Hheap with ⟨Hheap, Hcell, _⟩
  imodintro
  iframe Hheap
  iintro Hheap
  rw [ITree.bind_ret, ITree.bind_ret]
  isimp only [cell] at Hcont
  ispecialize Hcont $$ %(fresh heap) Hcell
  ispecialize Hcont $$ %(Iris.Std.insert (M := HeapMap) heap (fresh heap) (some value)) Hheap
  iexact Hcont

private theorem bind_ret_right {ρ : Type} (t : ITree (StateE (Heap V)) ρ) :
    ITree.bind t ret = t := by
  change (t >>= pure) = t
  simp

theorem wp_load (location : Nat) (fraction : DFrac) (value : Option V)
    (Φ : Option V → IProp GF) :
    iprop(cell (GF := GF) location fraction value ∗
      (cell location fraction value -∗ Φ value)) ⊢ wp (load location) Φ := by
  rw [← bind_ret_right (load location)]
  iintro ⟨Hcell, Hcont⟩
  iapply wp_load_bind location fraction value ret
  iframe Hcell
  iintro Hcell
  iapply wp_ret
  iapply Hcont $$ Hcell

theorem wp_store' (location : Nat) (old next : Option V) (Φ : Option V → IProp GF) :
    iprop(cell (GF := GF) location (.own 1) old ∗
      (cell location (.own 1) next -∗ Φ old)) ⊢ wp (store' location next) Φ := by
  rw [← bind_ret_right (store' location next)]
  iintro ⟨Hcell, Hcont⟩
  iapply wp_store'_bind location old next ret
  iframe Hcell
  iintro Hcell
  iapply wp_ret
  iapply Hcont $$ Hcell

theorem wp_store (location : Nat) (old : Option V) (next : V)
    (Φ : Option V → IProp GF) :
    iprop(cell (GF := GF) location (.own 1) old ∗
      (cell location (.own 1) (some next) -∗ Φ old)) ⊢ wp (store location next) Φ :=
  wp_store' location old (some next) Φ

theorem wp_free (location : Nat) (old : Option V) (Φ : Option V → IProp GF) :
    iprop(cell (GF := GF) location (.own 1) old ∗
      (cell location (.own 1) none -∗ Φ old)) ⊢ wp (free location) Φ :=
  wp_store' location old none Φ

theorem wp_alloc (value : V) (Φ : Nat → IProp GF) :
    iprop(∀ location : Nat, cell (GF := GF) location (.own 1) (some value) -∗ Φ location) ⊢
      wp (alloc value) Φ := by
  rw [← bind_ret_right (alloc value)]
  iintro Hcont
  iapply wp_alloc_bind value ret
  iintro %location Hcell
  iapply wp_ret
  iapply Hcont $$ %location Hcell

theorem load_spec (location : Nat) (fraction : DFrac) (value : Option V) :
    cell (GF := GF) location fraction value ⊢
      wp (load location) (fun r => iprop(⌜r = value⌝ ∗ cell location fraction value)) := by
  iintro Hcell
  iapply wp_load location fraction value
  iframe Hcell
  iintro Hcell
  iframe Hcell
  itrivial

theorem store_spec (location : Nat) (old : Option V) (next : V) :
    cell (GF := GF) location (.own 1) old ⊢
      wp (store location next)
        (fun r => iprop(⌜r = old⌝ ∗ cell location (.own 1) (some next))) := by
  iintro Hcell
  iapply wp_store location old next
  iframe Hcell
  iintro Hcell
  iframe Hcell
  itrivial

theorem free_spec (location : Nat) (old : Option V) :
    cell (GF := GF) location (.own 1) old ⊢
      wp (free location) (fun r => iprop(⌜r = old⌝ ∗ cell location (.own 1) none)) := by
  iintro Hcell
  iapply wp_free location old
  iframe Hcell
  iintro Hcell
  iframe Hcell
  itrivial

theorem alloc_spec (value : V) :
    ⊢ wp (GF := GF) (alloc value) (fun location => cell location (.own 1) (some value)) := by
  iapply wp_alloc
  iintro %location Hcell
  iexact Hcell

/-- A changed value is observed by the next read, while unrelated ownership
survives the entire sequence. This uses the continuation rules, not an
interpreter-specific evaluation lemma. -/
theorem store_load_spec (location : Nat) (old : Option V) (next : V) (R : IProp GF) :
    iprop(cell location (.own 1) old ∗ R) ⊢
      wp ((store location next).bind fun _ => load location)
        (fun r => iprop(⌜r = some next⌝ ∗ cell location (.own 1) (some next) ∗ R)) := by
  iintro ⟨Hcell, HR⟩
  unfold store
  iapply wp_store'_bind location old (some next)
  iframe Hcell
  iintro Hcell
  iapply wp_load location (.own 1) (some next)
  iframe Hcell
  iintro Hcell
  iframe Hcell HR
  itrivial

/-- Allocation, mutation, and reading compose without assuming initial ownership. -/
theorem alloc_store_load_spec (first next : V) :
    ⊢ wp (GF := GF)
      ((alloc first).bind fun location =>
        (store location next).bind fun _ =>
          (load location).bind fun value => ret (location, value))
      (fun result => iprop(⌜result.2 = some next⌝ ∗
        cell result.1 (.own 1) (some next))) := by
  iapply wp_alloc_bind first
  iintro %location Hcell
  unfold store
  iapply wp_store'_bind location (some first) (some next)
  iframe Hcell
  iintro Hcell
  iapply wp_load_bind location (.own 1) (some next)
  iframe Hcell
  iintro Hcell
  iapply wp_ret
  iframe Hcell
  itrivial

end Logic

section Initialization

variable {V : Type} {GF : BundledGFunctors} {hlc : HasLC}
variable [InvGS_gen hlc GF] [genHeapPreS Nat (Option V) GF HeapMap]

/-- Allocate the standard ghost heap and full ownership of every initial cell.
This constructs the resources; agreement and updates above are proved from
the concrete Iris model rather than postulated as heap-specific axioms. -/
theorem init (heap : Heap V) :
    ⊢ (iprop(|={∅}=> ∃ G : genHeapGS Nat (Option V) GF HeapMap,
      authority (G := G) heap ∗
      (Iris.BI.bigSepM (M := HeapMap) (fun location value => cell (G := G) location (.own 1) value) heap)) : IProp GF) := by
  imod genHeap_init (H := HeapMap) heap with ⟨%G, Hheap, Hcells, _⟩
  imodintro
  iexists G
  isimp only [authority, cell]
  iframe

end Initialization

end ProgramLogicCarte.OwnershipHeap
