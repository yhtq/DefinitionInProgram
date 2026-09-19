import ProgramLogicCarte.Wpi
import ITree.UpToTaus

/-!
# Logical steps

`StepE` marks semantic progress.  Its handler can interpret a step either as
the identity modality or as Iris' later modality.  `stepIfn` erases step
events, optionally stopping after a finite step budget.
-/

namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE ITree

universe u uρ

inductive StepE : Type u → Type u where
  | step : StepE (ULift Unit)

def step {ε : Type u → Type u} (inject : StepE ⟶ ε) : ITree ε (ULift Unit) :=
  trigger (inject .step)

inductive LaterModality where
  | identity
  | later
deriving DecidableEq

def lat {GF : BundledGFunctors} : LaterModality → IProp GF → IProp GF
  | .identity, P => P
  | .later, P => iprop(▷ P)

theorem lat_ne {GF : BundledGFunctors} {n : Nat} (m : LaterModality)
    {P Q : IProp GF} (h : P ≡{n}≡ Q) : lat m P ≡{n}≡ lat m Q := by
  cases m with
  | identity => exact h
  | later => exact later_ne.ne h

def stepHandle {GF : BundledGFunctors} (m : LaterModality)
    {α : Type u} (e : StepE α) (Φ : α → IProp GF) : IProp GF :=
  match e with
  | .step => lat m (Φ (.up ()))

def stepH {GF : BundledGFunctors} (m : LaterModality) : IHandler GF StepE where
  handle e Φ _ := stepHandle m e Φ
  mono e := by
    cases e
    intro Φ Φ' spawned spawned'
    cases m with
    | identity =>
        simp only [stepHandle, lat]
        istart
        iintro HΦ _ H
        iapply HΦ $$ H
    | later =>
        simp only [stepHandle, lat]
        istart
        iintro HΦ _ H
        inext
        iapply HΦ $$ H
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    cases e
    exact lat_ne m (hΦ (.up ()))

instance stepHSequential {GF : BundledGFunctors} (m : LaterModality) :
    IHandler.Sequential (stepH (GF := GF) m) where
  sequential e Φ spawned := by
    cases e
    exact .rfl

/-- Empty-mask WP rule for one logical step. -/
theorem wpi_step {GF : BundledGFunctors} [InvGS_gen hlc GF]
    (m : LaterModality) (Φ : ULift Unit → IProp GF) :
    lat m (fupd ∅ ∅ (Φ (.up ()))) ⊢ wpi (stepH m) (step (fun e => e)) Φ := by
  rw [step, trigger, wpi_vis]
  istart
  iintro Hstep
  imodintro
  isimp only [stepH, stepHandle]
  rw [wpi_ret]
  iexact Hstep

inductive StepExhausted where
  | exhausted
deriving DecidableEq

/-- Erase logical steps.  `none` gives an unbounded interpreter; `some n`
returns `StepExhausted` when the next step would exceed the budget. -/
def stepIfn {ε : Type u → Type u} {ρ : Type uρ}
    (fuel : Option Nat) (t : ITree (StepE + ε) ρ) :
    ITree ε (Sum ρ StepExhausted) :=
  .corecEmbed (fun (st : Option Nat × ITree (StepE + ε) ρ) =>
    let (fuel, t) := st
    match t.dest with
    | ⟨.ret x, _⟩ => .inl (ret (.inl x))
    | ⟨.tau, c⟩ => .inr (tau' (.inr (fuel, c 0)))
    | ⟨.vis _ (.inl .step), k⟩ =>
        match fuel with
        | some 0 => .inl (ret (.inr .exhausted))
        | some (n + 1) => .inr (tau' (.inr (some n, k (.up ()))))
        | none => .inr (tau' (.inr (none, k (.up ()))))
    | ⟨.vis _ (.inr e), k⟩ =>
        .inr (vis' e (fun x => .inr (fuel, k x))))
    (fuel, t)

def StepIrel {ε : Type u → Type u} {ρ : Type uρ}
    (fuel : Option Nat) (t : ITree (StepE + ε) ρ)
    (t' : ITree ε (Sum ρ StepExhausted)) : Prop :=
  t' = stepIfn fuel t

theorem stepIfn_irel {ε : Type u → Type u} {ρ : Type uρ}
    (fuel : Option Nat) (t : ITree (StepE + ε) ρ) :
    StepIrel fuel t (stepIfn fuel t) :=
  rfl

@[simp]
theorem stepIfn_ret {ε : Type u → Type u} {ρ : Type uρ}
    (fuel : Option Nat) (x : ρ) :
    stepIfn (ε := ε) fuel (ret x) = ret (.inl x) := by
  conv => lhs; simp only [stepIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem stepIfn_tau {ε : Type u → Type u} {ρ : Type uρ}
    (fuel : Option Nat) (t : ITree (StepE + ε) ρ) :
    stepIfn fuel (tau t) = tau (stepIfn fuel t) := by
  conv => lhs; simp only [stepIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem stepIfn_step_zero {ε : Type u → Type u} {ρ : Type uρ}
    (k : ULift Unit → ITree (StepE + ε) ρ) :
    stepIfn (some 0) (vis (SumE.inl StepE.step) k) =
      @ret ε (Sum ρ StepExhausted) (.inr .exhausted) := by
  conv => lhs; simp only [stepIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem stepIfn_step_succ {ε : Type u → Type u} {ρ : Type uρ}
    (n : Nat) (k : ULift Unit → ITree (StepE + ε) ρ) :
    stepIfn (some (n + 1)) (vis (SumE.inl StepE.step) k) =
      tau (stepIfn (some n) (k (.up ()))) := by
  conv => lhs; simp only [stepIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem stepIfn_step_unbounded {ε : Type u → Type u} {ρ : Type uρ}
    (k : ULift Unit → ITree (StepE + ε) ρ) :
    stepIfn none (vis (SumE.inl StepE.step) k) =
      tau (stepIfn none (k (.up ()))) := by
  conv => lhs; simp only [stepIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem stepIfn_vis {ε : Type u → Type u} {ρ : Type uρ} {α : Type u}
    (fuel : Option Nat) (e : ε α) (k : α → ITree (StepE + ε) ρ) :
    stepIfn fuel (vis (SumE.inr e) k) =
      vis e (fun x => stepIfn fuel (k x)) := by
  conv => lhs; simp only [stepIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

end ProgramLogicCarte
