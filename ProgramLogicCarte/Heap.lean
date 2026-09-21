import ProgramLogicCarte.State
import ProgramLogicCarte.Interpreter

/-!
# Executable finite heaps

The heap effect in the Coq development is a state effect whose cells may be
allocated, deallocated, or absent.  Here a finite list supplies the executable
representation; locations are natural numbers and out-of-range accesses return
`none` without changing the heap.
-/

namespace ProgramLogicCarte

open ITree

universe u

abbrev Heap (V : Type u) := List (Option V)

def Heap.read : Heap V → Nat → Option V
  | [], _ => none
  | value :: _, 0 => value
  | _ :: tail, location + 1 => Heap.read tail location

def Heap.write (heap : Heap V) (location : Nat) (value : Option V) : Heap V :=
  match location, heap with
  | 0, _ :: tail => value :: tail
  | _ + 1, head :: tail => head :: Heap.write tail location value
  | _, [] => []

def heapLoad {V : Type u} {ε : Type u → Type u}
    (inject : StateE (Heap V) ⟶ ε) (location : Nat) : ITree ε (Option V) :=
  ITree.bind (getState inject) fun heap => ret (heap.read location)

def heapStore' {V : Type u} {ε : Type u → Type u}
    (inject : StateE (Heap V) ⟶ ε) (location : Nat) (value : Option V) :
    ITree ε (Option V) :=
  ITree.bind (getState inject) fun heap =>
  let old := heap.read location
  ITree.bind (setState inject (heap.write location value)) fun _ => ret old

def heapStore {V : Type u} {ε : Type u → Type u}
    (inject : StateE (Heap V) ⟶ ε) (location : Nat) (value : V) :
    ITree ε (Option V) :=
  heapStore' inject location (some value)

def heapAlloc {V : Type u} {ε : Type u → Type u}
    (inject : StateE (Heap V) ⟶ ε) (value : V) : ITree ε Nat :=
  ITree.bind (getState inject) fun heap =>
  let location := heap.length
  ITree.bind (setState inject (heap ++ [some value])) fun _ => ret location

@[simp]
theorem heap_read_nil (location : Nat) : Heap.read ([] : Heap V) location = none := by
  cases location <;> rfl

@[simp]
theorem heap_read_zero (tail : Heap V) (value : Option V) :
    Heap.read (value :: tail) 0 = value :=
  rfl

@[simp]
theorem heap_write_zero (tail : Heap V) (old value : Option V) :
    Heap.write (old :: tail) 0 value = value :: tail :=
  rfl

@[simp]
theorem heap_write_oob (value : Option V) (location : Nat) :
    Heap.write ([] : Heap V) location value = [] := by
  cases location <;> rfl

section Examples

open ITree

example : stateIfn [some 4]
    (heapLoad (V := Nat) (ε := StateE (Heap Nat) + VoidE) SumE.inl 0) =
    tau (ret ([some 4], some 4) : ITree VoidE (Heap Nat × Option Nat)) := by
  rw [heapLoad, getState, trigger, ITree.bind_vis, stateIfn_get,
    ITree.bind_ret, stateIfn_ret]
  simp

example : runVoid 2 (stateIfn [some 4]
    (heapLoad (V := Nat) (ε := StateE (Heap Nat) + (VoidE : Type → Type)) SumE.inl 0)) =
    some ([some 4], some 4) := by
  rw [show stateIfn [some 4]
      (heapLoad (V := Nat) (ε := StateE (Heap Nat) + (VoidE : Type → Type)) SumE.inl 0) =
      tau (ret ([some 4], some 4) : ITree (VoidE : Type → Type) (Heap Nat × Option Nat)) by
    rw [heapLoad, getState, trigger, ITree.bind_vis, stateIfn_get,
      ITree.bind_ret, stateIfn_ret]
    simp]
  rw [runVoid_tau, runVoid_ret]

end Examples

end ProgramLogicCarte
