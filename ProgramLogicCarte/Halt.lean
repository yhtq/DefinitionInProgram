import ProgramLogicCarte.Wpi
import ProgramLogicCarte.UndefinedBehavior

/-!
# Safe halting

Unlike undefined behavior, halting is a successful terminal effect.  Its
logical handler restores the full invariant mask.  The executable
interpretation records the halt in the return type.
-/

namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE ITree

universe u uρ

inductive HaltE : Type u → Type u where
  | halt : HaltE (EmptyAnswer : Type u)

/-- Emit a safe halt through an explicit effect embedding. -/
def halt {ε : Type u → Type u} {ρ : Type uρ} (inject : HaltE ⟶ ε) : ITree ε ρ :=
  vis (inject .halt) (fun x => nomatch x.down)

/-- Unwrap an option, halting safely on `none`. -/
def someOrHalt {ε : Type u → Type u} {ρ : Type uρ}
    (inject : HaltE ⟶ ε) : Option ρ → ITree ε ρ
  | some x => ret x
  | none => halt inject

/-- Assume a decidable proposition; a false assumption safely halts. -/
def assumeOrHalt {ε : Type u → Type u} (inject : HaltE ⟶ ε)
    (P : Prop) [Decidable P] : ITree ε (PLift P) :=
  if h : P then ret ⟨h⟩ else halt inject

/-- Safe halting closes the empty invariant mask and establishes `True`. -/
def haltH {GF : BundledGFunctors} [InvGS_gen hlc GF] : IHandler GF HaltE where
  handle _ _ _ := fupd ∅ ⊤ iprop(True)
  mono _ := by
    intro Φ Φ' spawned spawned'
    istart
    iintro _ _ HHalt
    iexact HHalt
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    exact .rfl

instance haltHSequential {GF : BundledGFunctors} [InvGS_gen hlc GF] :
    IHandler.Sequential (haltH : IHandler GF HaltE) where
  sequential := by
    intro α e Φ spawned
    exact .rfl

inductive Halted where
  | halted
deriving DecidableEq

/-- Execute halt events, returning `Halted`; unrelated effects remain visible. -/
def haltIfn {ε : Type u → Type u} {ρ : Type uρ}
    (t : ITree (HaltE + ε) ρ) : ITree ε (Sum ρ Halted) :=
  .corecEmbed (fun t =>
    match t.dest with
    | ⟨.ret x, _⟩ => .inl (ret (.inl x))
    | ⟨.tau, c⟩ => .inr (tau' (.inr (c 0)))
    | ⟨.vis _ (.inl .halt), _⟩ => .inl (ret (.inr .halted))
    | ⟨.vis _ (.inr e), k⟩ => .inr (vis' e (fun x => .inr (k x)))) t

def HaltIrel {ε : Type u → Type u} {ρ : Type uρ}
    (t : ITree (HaltE + ε) ρ) (t' : ITree ε (Sum ρ Halted)) : Prop :=
  t' = haltIfn t

theorem haltIfn_irel {ε : Type u → Type u} {ρ : Type uρ}
    (t : ITree (HaltE + ε) ρ) : HaltIrel t (haltIfn t) :=
  rfl

@[simp]
theorem haltIfn_ret {ε : Type u → Type u} {ρ : Type uρ} (x : ρ) :
    haltIfn (ε := ε) (ret x) = ret (.inl x) := by
  conv => lhs; simp only [haltIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem haltIfn_tau {ε : Type u → Type u} {ρ : Type uρ}
    (t : ITree (HaltE + ε) ρ) :
    haltIfn (tau t) = tau (haltIfn t) := by
  conv => lhs; simp only [haltIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem haltIfn_halt {ε : Type u → Type u} {ρ : Type uρ}
    (k : EmptyAnswer → ITree (HaltE + ε) ρ) :
    haltIfn (vis (SumE.inl HaltE.halt) k) =
      @ret ε (Sum ρ Halted) (.inr .halted) := by
  conv => lhs; simp only [haltIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem haltIfn_vis {ε : Type u → Type u} {ρ : Type uρ} {α : Type u}
    (e : ε α) (k : α → ITree (HaltE + ε) ρ) :
    haltIfn (vis (SumE.inr e) k) = vis e (fun x => haltIfn (k x)) := by
  conv => lhs; simp only [haltIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem assumeOrHalt_of_true {ε : Type u → Type u} (inject : HaltE ⟶ ε)
    {P : Prop} [Decidable P] (h : P) :
    assumeOrHalt inject P = ret ⟨h⟩ := by
  simp [assumeOrHalt, h]

@[simp]
theorem assumeOrHalt_of_false {ε : Type u → Type u} (inject : HaltE ⟶ ε)
    {P : Prop} [Decidable P] (h : ¬ P) :
    assumeOrHalt inject P = halt inject := by
  simp [assumeOrHalt, h]

end ProgramLogicCarte
