import ProgramLogicCarte.Rules

/-!
# Small executable-proof smoke tests

These examples deliberately use only a single event and its direct logical
handler.  They check that the event constructors, handler interfaces, WPi
unfolding, and concrete rules agree at their boundary.
-/

namespace ProgramLogicCarte.Examples

open Iris Iris.BI ITree
open ExampleLang

universe u

/-- A concrete nondeterministic program.  The event records `0` as the
default resolution, so `demonicIfn` deterministically returns `1`. -/
def pickThenSucc : ITree (DemonicE + (VoidE : Type → Type 1)) Int :=
  vis (SumE.inl (.choose Int 0)) (fun n => ret (n + 1))

example :
    subst "x" (.lit (.int 3)) (.plus (.var "x") (.var "y")) =
      .plus (.val (.lit (.int 3))) (.var "y") := by
  simp [subst]

example :
    substBinder (.named "x") (.lit (.int 3)) (.var "x") = .val (.lit (.int 3)) := by
  simp

theorem pickThenSucc_runs :
    demonicIfn pickThenSucc = tau (ret 1 : ITree (VoidE : Type → Type 1) Int) := by
  rw [show pickThenSucc = vis (SumE.inl (.choose Int 0)) (fun n => ret (n + 1)) from rfl]
  rw [demonicIfn_choose, demonicIfn_ret]
  simp

example : runVoid 2 (demonicIfn pickThenSucc) = some 1 := by
  rw [pickThenSucc_runs]
  exact runVoid_tau 1 (ret 1)

/-- Read the state, increment it, then return the original value. -/
def readThenIncrement : ITree (StateE Nat + VoidE) Nat :=
  vis (SumE.inl StateE.get) fun s =>
    vis (SumE.inl (.set (s + 1))) fun _ => ret s

theorem readThenIncrement_runs :
    stateIfn 7 readThenIncrement = tau (tau (ret (8, 7) : ITree VoidE (Nat × Nat))) := by
  rw [show readThenIncrement =
    vis (SumE.inl StateE.get) (fun s =>
      vis (SumE.inl (.set (s + 1))) (fun _ => ret s)) from rfl]
  rw [stateIfn_get, stateIfn_set, stateIfn_ret]

example : runVoid 3 (stateIfn 7 readThenIncrement) = some (8, 7) := by
  rw [readThenIncrement_runs]
  rw [runVoid_tau, runVoid_tau, runVoid_ret]

/-- One bounded logical step followed by a return. -/
def countedStep : ITree (StepE + VoidE) Nat :=
  vis (SumE.inl StepE.step) fun _ => ret 42

theorem countedStep_runs :
    stepIfn (some 1) countedStep = tau (ret (.inl 42) : ITree VoidE (Sum Nat StepExhausted)) := by
  rw [show countedStep = vis (SumE.inl StepE.step) (fun _ => ret 42) from rfl]
  rw [stepIfn_step_succ, stepIfn_ret]

example : runVoid 2 (stepIfn (some 1) countedStep) = some (.inl 42) := by
  rw [countedStep_runs, runVoid_tau, runVoid_ret]

/-- A safe halt and undefined behavior produce distinct executable outcomes. -/
def safeStop : ITree (HaltE + VoidE) Nat :=
  vis (SumE.inl HaltE.halt) fun impossible => nomatch impossible.down

def badStop : ITree (UbE + VoidE) Nat :=
  vis (SumE.inl UbE.crash) fun impossible => nomatch impossible.down

example : haltIfn safeStop = ret (.inr .halted : Sum Nat Halted) := by
  rw [show safeStop = vis (SumE.inl HaltE.halt) (fun impossible => nomatch impossible.down) from rfl]
  rw [haltIfn_halt]

example : ubIfn badStop = ret (.inr .crash : Sum Nat UbCrash) := by
  rw [show badStop = vis (SumE.inl UbE.crash) (fun impossible => nomatch impossible.down) from rfl]
  rw [ubIfn_crash]

example : runVoid 1 (haltIfn safeStop) = some (.inr .halted : Sum Nat Halted) := by
  rw [show haltIfn safeStop = ret (.inr .halted : Sum Nat Halted) by
    rw [show safeStop = vis (SumE.inl HaltE.halt) (fun impossible => nomatch impossible.down) from rfl]
    rw [haltIfn_halt]]
  exact runVoid_ret 0 _

example : runVoid 1 (ubIfn badStop) = some (.inr .crash : Sum Nat UbCrash) := by
  rw [show ubIfn badStop = ret (.inr .crash : Sum Nat UbCrash) by
    rw [show badStop = vis (SumE.inl UbE.crash) (fun impossible => nomatch impossible.down) from rfl]
    rw [ubIfn_crash]]
  exact runVoid_ret 0 _

example {GF : BundledGFunctors} [InvGS_gen hlc GF]
    (α : Type u) [Inhabited α] (Φ : α → IProp GF) :
    iprop(∀ x, Φ x) ⊢ wpi demonicH (demonicChoice α) Φ :=
  wpi_demonicChoice α Φ

example {GF : BundledGFunctors} [InvGS_gen hlc GF]
    (α : Type u) (chosen : α) (Φ : α → IProp GF) :
    Φ chosen ⊢ wpi angelicH (angelicChoice α) Φ :=
  wpi_angelicChoice α chosen Φ

example {GF : BundledGFunctors} [InvGS_gen hlc GF]
    (m : LaterModality) (Φ : ULift Unit → IProp GF) :
    lat m (fupd ∅ ∅ (Φ (.up ()))) ⊢
      wpi (stepH m) (step (fun e => e)) Φ :=
  wpi_step m Φ

example {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {S : Type u} [StateInterp GF S] (Φ : S → IProp GF) :
    iprop(∀ s, interp (GF := GF) (S := S) s ={∅}=∗
      interp (GF := GF) (S := S) s ∗ Φ s) ⊢
      wpi (stateH S) (getState (fun e => e)) Φ :=
  wpi_getState Φ

example {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {S : Type u} [StateInterp GF S] (next : S)
    (Φ : ULift Unit → IProp GF) :
    iprop(∀ s, interp (GF := GF) (S := S) s ={∅}=∗
      interp (GF := GF) (S := S) next ∗ Φ (.up ())) ⊢
      wpi (stateH S) (setState (fun e => e) next) Φ :=
  wpi_setState next Φ

example {ε : Type u → Type u} {ρ : Type u}
    (k : EmptyAnswer → ITree (HaltE + ε) ρ) :
    haltIfn (vis (SumE.inl HaltE.halt) k) =
      @ret ε (Sum ρ Halted) (.inr .halted) :=
  haltIfn_halt k

example {ε : Type u → Type u} {ρ : Type u}
    (n : Nat) (k : ULift Unit → ITree (StepE + ε) ρ) :
    stepIfn (some (n + 1)) (vis (SumE.inl StepE.step) k) =
      tau (stepIfn (some n) (k (.up ()))) :=
  stepIfn_step_succ n k

example {ρ : Type u} (x : ρ) :
    runVoid 1 (ret x : ITree (VoidE : Type u → Type u) ρ) = some x :=
  runVoid_ret 0 x

example {ρ : Type u} (x : ρ) :
    IEqutt (ret x : ITree (VoidE : Type u → Type u) ρ) (ret x) :=
  runVoid_spec 1 (ret x) x rfl

end ProgramLogicCarte.Examples
