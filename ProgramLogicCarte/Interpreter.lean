import ITree.UpToTaus

/-!
# Finite execution of effect-free trees

This is the executable fragment from `src/interpreter.v`.  A finite fuel
counter can only traverse silent steps; visible `VoidE` events are impossible.
Successful execution is certified by weak tree equivalence to the returned
value.
-/

namespace ProgramLogicCarte

open ITree

universe u v uρ

def runVoid {ρ : Type uρ} : Nat → ITree (VoidE : Type u → Type v) ρ → Option ρ
  | 0, _ => none
  | Nat.succ fuel, t =>
      match t.dest with
      | ⟨.ret x, _⟩ => some x
      | ⟨.tau, c⟩ => runVoid fuel (c 0)
      -- This branch is unreachable for `VoidE`; returning `none` keeps the
      -- executable total without relying on an empty-type eliminator.
      | ⟨.vis _ _, _⟩ => none

@[simp]
theorem runVoid_zero {ρ : Type uρ} (t : ITree (VoidE : Type u → Type v) ρ) :
    runVoid 0 t = none :=
  rfl

@[simp]
theorem runVoid_ret {ρ : Type uρ} (fuel : Nat) (x : ρ) :
    runVoid (fuel + 1) (ret x : ITree (VoidE : Type u → Type v) ρ) = some x :=
  rfl

@[simp]
theorem runVoid_tau {ρ : Type uρ} (fuel : Nat)
    (t : ITree (VoidE : Type u → Type v) ρ) :
    runVoid (fuel + 1) (tau t) = runVoid fuel t :=
  rfl

/-- A successful finite execution is a weak-bisimulation certificate. -/
theorem runVoid_spec {ρ : Type uρ} (fuel : Nat)
    (t : ITree (VoidE : Type u → Type v) ρ) (r : ρ) :
    runVoid fuel t = some r → IEqutt t (ret r) := by
  induction fuel generalizing t with
  | zero =>
      simp only [runVoid]
      intro h
      nomatch h
  | succ fuel ih =>
      apply t.dMatchOn
      · intro x hx h
        rw [hx] at h ⊢
        simp only [runVoid] at h
        obtain rfl := Option.some.inj h
        exact iequtt_ret x
      · intro next hx h
        rw [hx] at h ⊢
        simp only [runVoid] at h
        exact iequtt_tau_left (ih next h)
      · intro α e k hx h
        rw [hx] at h
        simp only [runVoid] at h
        nomatch h

end ProgramLogicCarte
