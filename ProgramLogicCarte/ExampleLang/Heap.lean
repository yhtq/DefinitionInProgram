import ProgramLogicCarte.ExampleLang.Syntax
import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Sort

/-! Finite-map heap representation for the source ExampleLang. -/
namespace ProgramLogicCarte.ExampleLang

/-- A finite map from integer locations to optional values. A missing key
differs from a present key mapped to `none`, matching Coq's
`gmap loc (option val)`. -/
abbrev ExampleHeap := Finmap (fun _ : Int => Option Value)

/-- The mathlib finite map has computable equality and an empty default. -/
example : DecidableEq ExampleHeap := inferInstance
example : Inhabited ExampleHeap := inferInstance

def ExampleHeap.lookup (heap : ExampleHeap) (location : Int) :
    Option (Option Value) :=
  Finmap.lookup location heap

def ExampleHeap.read (heap : ExampleHeap) (location : Int) : Option Value :=
  (heap.lookup location).join

def ExampleHeap.write (heap : ExampleHeap) (location : Int)
    (value : Option Value) : ExampleHeap :=
  Finmap.insert location value heap

/-- A location strictly above every key in the finite map. -/
def ExampleHeap.fresh (heap : ExampleHeap) : Int :=
  (heap.keys.sort (· ≤ ·)).foldl (fun next key => max next (key + 1)) 0

@[simp] theorem ExampleHeap.lookup_empty (location : Int) :
    ExampleHeap.lookup (∅ : ExampleHeap) location = none := by
  exact Finmap.lookup_empty location

@[simp] theorem ExampleHeap.read_empty (location : Int) :
    ExampleHeap.read (∅ : ExampleHeap) location = none := by
  simp [ExampleHeap.read]

@[simp] theorem ExampleHeap.lookup_write_same (heap : ExampleHeap)
    (location : Int) (value : Option Value) :
    (heap.write location value).lookup location = some value := by
  exact Finmap.lookup_insert heap

@[simp] theorem ExampleHeap.read_write_same (heap : ExampleHeap)
    (location : Int) (value : Option Value) :
    (heap.write location value).read location = value := by
  simp [ExampleHeap.read]

/-- An allocated free cell is distinguishable from an absent address. -/
example : (Finmap.singleton 4 none : ExampleHeap).lookup 4 = some none := by
  exact Finmap.lookup_singleton_eq
example : (∅ : ExampleHeap).lookup 4 = none := by
  simp

/-- Updating an absent address creates an entry, as Coq's map insertion does. -/
example (value : Value) :
    (ExampleHeap.write (∅ : ExampleHeap) 4 (some value)).lookup 4 =
      some (some value) := by
  simp

/-- Allocation uses a computable fresh location, even after inserting a
present-but-free cell. -/
example : ExampleHeap.fresh (Finmap.singleton 4 none : ExampleHeap) = 5 := by
  native_decide

/-- Coq locations include negative integers; they remain distinct from
nonnegative addresses in the heap. -/
example (value : Value) :
    (ExampleHeap.write (∅ : ExampleHeap) (-3) (some value)).read (-3) =
      some value := by
  simp

/-- Updating one location leaves every other lookup unchanged. -/
theorem ExampleHeap.lookup_write_other (heap : ExampleHeap)
    (location other : Int) (value : Option Value) (h : location ≠ other) :
    (heap.write location value).lookup other = heap.lookup other := by
  exact Finmap.lookup_insert_of_ne heap (Ne.symm h)

private theorem freshFold_ge (keys : List Int) (start : Int) :
    start ≤ keys.foldl (fun next key => max next (key + 1)) start := by
  induction keys generalizing start with
  | nil => exact le_refl _
  | cons key rest ih =>
      simp only [List.foldl_cons]
      exact le_trans (le_max_left _ _) (ih _)

private theorem freshFold_gt :
    ∀ (keys : List Int) (start location : Int),
      location ∈ keys →
      location < keys.foldl (fun next key => max next (key + 1)) start := by
  intro keys
  induction keys with
  | nil =>
      intro start location hmem
      simp at hmem
  | cons key rest ih =>
      intro start location hmem
      simp only [List.mem_cons] at hmem
      simp only [List.foldl_cons]
      rcases hmem with heq | hrest
      · subst location
        exact lt_of_lt_of_le (by omega)
          (le_trans (le_max_right _ _) (freshFold_ge rest _))
      · exact ih _ _ hrest

theorem ExampleHeap.fresh_gt (heap : ExampleHeap) (location : Int)
    (hmem : location ∈ heap.keys) : location < heap.fresh := by
  exact freshFold_gt (heap.keys.sort (· ≤ ·)) 0 location ((Finset.mem_sort (s := heap.keys) (r := (· ≤ ·))).mpr hmem)

theorem ExampleHeap.lookup_some_mem (heap : ExampleHeap) (location : Int)
    (value : Option Value) (h : heap.lookup location = some value) :
    location ∈ heap.keys := by
  exact (Finmap.mem_keys).mpr (Finmap.mem_of_lookup_eq_some h)

/-- Allocation's chosen location is not already mapped, including free cells. -/
theorem ExampleHeap.lookup_fresh (heap : ExampleHeap) :
    heap.lookup heap.fresh = none := by
  cases h : heap.lookup heap.fresh with
  | none => rfl
  | some value =>
      have hmem := heap.lookup_some_mem heap.fresh value h
      have hlt := heap.fresh_gt heap.fresh hmem
      exact False.elim (lt_irrefl _ hlt)

end ProgramLogicCarte.ExampleLang
