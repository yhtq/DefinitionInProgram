import ProgramLogicCarte.Handler
import ITree.UpToTaus

/-! Undefined behavior (`src/ub.v`, called `Fail` in the paper). -/

namespace ProgramLogicCarte

open Iris Iris.BI ITree

universe u uₑ

/-- Empty answer type lifted to the event signature's universe. -/
abbrev EmptyAnswer : Type u := ULift Empty

/-- The sole undefined-behavior event has no possible answer. -/
inductive UbE : Type u → Type u where
  | crash : UbE EmptyAnswer

/-- Emit undefined behavior through an explicit effect embedding. -/
def ub {ε : Type u → Type u} {ρ : Type uₑ} (inject : UbE ⟶ ε) : ITree ε ρ :=
  vis (inject .crash) (fun x => nomatch x.down)

/-- Unwrap an option, exhibiting undefined behavior on `none`. -/
def someOrUb {ε : Type u → Type u} {ρ : Type uₑ}
    (inject : UbE ⟶ ε) : Option ρ → ITree ε ρ
  | some x => ret x
  | none => ub inject

/-- The logical handler makes undefined behavior unprovable. -/
def ubH {GF : BundledGFunctors} : IHandler GF UbE where
  handle _ _ _ := iprop(False)
  mono _ := by
    intro Φ Φ' spawned spawned'
    istart
    iintro _ _ HFalse
    iexact HFalse
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    exact .rfl

instance ubHSequential {GF : BundledGFunctors} :
    IHandler.Sequential (ubH : IHandler GF UbE) where
  sequential := by
    intro α e Φ spawned
    exact .rfl

/-- Marker returned when the executable interpreter encounters UB. -/
inductive UbCrash where
  | crash
deriving DecidableEq

/-- Interpret `UbE` by terminating with `UbCrash`; all other events remain
visible. -/
def ubIfn {ε : Type u → Type u} {ρ : Type uₑ}
    (t : ITree (UbE + ε) ρ) : ITree ε (Sum ρ UbCrash) :=
  .corecEmbed (fun t =>
    match t.dest with
    | ⟨.ret x, _⟩ => .inl (ret (.inl x))
    | ⟨.tau, c⟩ => .inr (tau' (.inr (c 0)))
    | ⟨.vis _ (.inl .crash), _⟩ => .inl (ret (.inr .crash))
    | ⟨.vis _ (.inr e), k⟩ => .inr (vis' e (fun x => .inr (k x)))) t

/-- The relational presentation used by adequacy statements. -/
def UbIrel {ε : Type u → Type u} {ρ : Type uₑ}
    (t : ITree (UbE + ε) ρ) (t' : ITree ε (Sum ρ UbCrash)) : Prop :=
  t' = ubIfn t

theorem ubIfn_irel {ε : Type u → Type u} {ρ : Type uₑ}
    (t : ITree (UbE + ε) ρ) : UbIrel t (ubIfn t) :=
  rfl

@[simp]
theorem ubIfn_ret {ε : Type u → Type u} {ρ : Type uₑ} (x : ρ) :
    ubIfn (ε := ε) (ret x) = ret (.inl x) := by
  conv => lhs; simp only [ubIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem ubIfn_tau {ε : Type u → Type u} {ρ : Type uₑ}
    (t : ITree (UbE + ε) ρ) :
    ubIfn (tau t) = tau (ubIfn t) := by
  conv => lhs; simp only [ubIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem ubIfn_crash {ε : Type u → Type u} {ρ : Type uₑ}
    (k : EmptyAnswer → ITree (UbE + ε) ρ) :
    ubIfn (vis (SumE.inl UbE.crash) k) =
      @ret ε (Sum ρ UbCrash) (.inr .crash) := by
  conv => lhs; simp only [ubIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem ubIfn_vis {ε : Type u → Type u} {ρ : Type uₑ} {α : Type u}
    (e : ε α) (k : α → ITree (UbE + ε) ρ) :
    ubIfn (vis (SumE.inr e) k) = vis e (fun x => ubIfn (k x)) := by
  conv => lhs; simp only [ubIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

/-- Assert a decidable proposition, exhibiting UB when it is false. -/
def assertOrUb {ε : Type u → Type u} (inject : UbE ⟶ ε)
    (P : Prop) [Decidable P] : ITree ε Unit :=
  if P then ret () else ub inject

theorem assertOrUb_of_true {ε : Type u → Type u} (inject : UbE ⟶ ε)
    {P : Prop} [Decidable P] (h : P) :
    assertOrUb inject P = ret () := by
  simp [assertOrUb, h]

theorem assertOrUb_of_false {ε : Type u → Type u} (inject : UbE ⟶ ε)
    {P : Prop} [Decidable P] (h : ¬ P) :
    assertOrUb inject P = ub inject := by
  simp [assertOrUb, h]

end ProgramLogicCarte
