import ProgramLogicCarte.StateAdequacy
import Iris.Instances.Lib.GhostMap
import Iris.Instances.Lib.Invariants

/-! Heap adequacy specialized from relational state adequacy, following
`src/heap.v`: the heap interpretation contains one half of a ghost-map
authority and a persistent invariant containing the other half. The logical
handler is the ordinary `stateH`, not an ownership-taking handler. -/

namespace ProgramLogicCarte.HeapLogic

open Iris Iris.BI ITree Iris.Std Iris.Std.PartialMap

/-- Finite locations with a separate `none` value for a freed cell. Absence
from the map represents an unallocated location. -/
abbrev HeapMap := fun V : Type => Std.ExtTreeMap Nat V compare
abbrev Heap (V : Type) := HeapMap (Option V)
abbrev HeapE (V : Type) := StateE (Heap V)

variable {V : Type} {GF : BundledGFunctors} {hlc : HasLC}
variable [InvGS_gen hlc GF] [GhostMapG GF Nat (Option V) HeapMap]

private def half : DFrac := .own ((1 : Qp).half)

/-- The full cell fragment; independent of the heap authority's fraction. -/
def pointsTo (γ : GName) (location : Nat) (dq : DFrac) (value : Option V) : IProp GF :=
  ghost_map_elem (H := HeapMap) γ dq location value

/-- The invariant hides the other authority half; it is not freely usable
ownership. -/
def heapInv (N : Namespace) (γ : GName) : IProp GF :=
  inv N (iprop(∃ heap : Heap V, ghost_map_auth (H := HeapMap) γ half heap))

/-- Coq `stateInterp_heap`: one half authority AND its invariant. -/
def heapState (N : Namespace) (γ : GName) (heap : Heap V) : IProp GF :=
  iprop(ghost_map_auth (H := HeapMap) γ half heap ∧ heapInv (V := V) N γ)

/-- Allocate a heap interpretation while retaining full fragments for all initial cells. -/
theorem heap_init (N : Namespace) (heap : Heap V) :
    ⊢ (iprop(|={⊤}=> ∃ γ : GName, heapState (V := V) N γ heap ∗
      (Iris.BI.bigSepM (M := HeapMap)
        (fun location value => pointsTo (V := V) γ location (.own 1) value) heap)) : IProp GF) := by
  imod ghost_map_alloc (H := HeapMap) heap with ⟨%γ, Hauth, Hcells⟩
  have hsplit : (ghost_map_auth (H := HeapMap) γ (.own (1 : Qp)) heap : IProp GF) ⊣⊢
      iprop(ghost_map_auth (H := HeapMap) γ half heap ∗
        ghost_map_auth (H := HeapMap) γ half heap) := by
    simpa only [half, Qp.half_add_half] using
      (Fractional.fractional (PROP := IProp GF)
        (Φ := fun q => ghost_map_auth (H := HeapMap) γ (.own q) heap)
        (1 : Qp).half (1 : Qp).half)
  icases hsplit.mp $$ Hauth with ⟨Hstate, HinvHalf⟩
  imod inv_alloc N ⊤
    (iprop(∃ current : Heap V, ghost_map_auth (H := HeapMap) γ half current))
    $$ [HinvHalf] with Hinv
  · inext
    iexists heap
    iexact HinvHalf
  · imodintro
    iexists γ
    isplitl [Hstate Hinv]
    · unfold heapState heapInv
      isplit
      · iexact Hstate
      · iexact Hinv
    · unfold pointsTo
      iexact Hcells

@[instance_reducible] def heapStateInterp (N : Namespace) (γ : GName) :
    StateInterp (IProp GF) (Heap V) where
  interp := heapState N γ

/-- Exactly the standard state handler instantiated at the heap type. -/
def heapH (N : Namespace) (γ : GName) : IHandlerBase (IProp GF) (HeapE V) :=
  letI := heapStateInterp (V := V) (GF := GF) N γ
  stateH (Heap V)

/-- The upstream heap relation is the state interpretation relation. -/
abbrev heapIrel {ε : Type → Type} {ρ : Type}
    (initial : Heap V) (source : ITree (HeapE V + ε) ρ)
    (target : ITree ε (Heap V × ρ)) : Prop :=
  StateIrel initial source target

/-- The masked WP of a heap program implies the masked WP of every related
interpreted tree, returning the final heap interpretation and postcondition. -/
theorem heap_adequacy {ε : Type → Type} {ρ : Type}
    (N : Namespace) (γ : GName) (H : IHandlerBase (IProp GF) ε)
    [IHandler.Sequential H] (initial : Heap V)
    (source : ITree (HeapE V + ε) ρ) (target : ITree ε (Heap V × ρ))
    (mask : CoPset) (Φ : ρ → IProp GF)
    (hrel : heapIrel initial source target) :
    iprop(heapState N γ initial ∗ wpiMask (heapH N γ ⊕ₕ H) mask source Φ) ⊢
    wpiMask H mask target (fun result => iprop(heapState N γ result.1 ∗ Φ result.2)) := by
  letI := heapStateInterp (V := V) (GF := GF) N γ
  exact stateIrel_adequacy H initial source target hrel mask Φ

/-- Functional execution satisfies the relation required by heap adequacy. -/
theorem heap_ifn_adequacy {ε : Type → Type} {ρ : Type}
    (N : Namespace) (γ : GName) (H : IHandlerBase (IProp GF) ε)
    [IHandler.Sequential H] (initial : Heap V)
    (source : ITree (HeapE V + ε) ρ) (mask : CoPset) (Φ : ρ → IProp GF) :
    iprop(heapState N γ initial ∗ wpiMask (heapH N γ ⊕ₕ H) mask source Φ) ⊢
    wpiMask H mask (stateIfn initial source)
      (fun result => iprop(heapState N γ result.1 ∗ Φ result.2)) := by
  letI := heapStateInterp (V := V) (GF := GF) N γ
  exact stateIfn_adequacy H initial source mask Φ

end ProgramLogicCarte.HeapLogic
