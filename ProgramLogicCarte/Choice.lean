import ProgramLogicCarte.Wpi
import ITree.UpToTaus

/-! Demonic nondeterminism (`src/choice.v`). -/

namespace ProgramLogicCarte

open Iris Iris.BI ITree

universe u

/-- An event that lets the environment choose any inhabitant of `α`.
`Inhabited α` is retained from the Coq development so that a deterministic
interpreter can always select a branch. -/
inductive DemonicE : Type u → Type (u + 1) where
  | choose (α : Type u) (default : α) : DemonicE α

/-- Emit one demonic-choice event. -/
def demonicChoice (α : Type u) [Inhabited α] : ITree DemonicE α :=
  trigger (.choose α default)

/-- The logical handler for demonic choice requires every branch to satisfy
its continuation condition. -/
def demonicH {GF : BundledGFunctors} : IHandler GF DemonicE where
  handle e Φ _ := match e with
    | .choose _ _ => iprop(∀ x, Φ x)
  mono e := by
    cases e
    intro Φ Φ' spawned spawned'
    istart
    iintro HΦ _ HAll
    iintro %x
    ispecialize HΦ $$ %x
    ispecialize HAll $$ %x
    iapply HΦ
    iexact HAll
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    cases e
    exact forall_ne hΦ

instance demonicHSequential {GF : BundledGFunctors} :
    IHandler.Sequential (demonicH : IHandler GF DemonicE) where
  sequential e Φ spawned := by
    cases e
    exact .rfl

/-- WP rule for a demonic choice handled directly by `demonicH`. -/
theorem wpi_demonicChoice {GF : BundledGFunctors} [InvGS_gen hlc GF]
    (α : Type u) [Inhabited α] (Φ : α → IProp GF) :
    iprop(∀ x, Φ x) ⊢ wpi demonicH (demonicChoice α) Φ := by
  rw [demonicChoice, trigger, wpi_vis]
  istart
  iintro HAll
  imodintro
  isimp only [demonicH]
  iintro %x
  rw [wpi_ret]
  imodintro
  ispecialize HAll $$ %x
  iexact HAll

/-- One-layer unfolding relation for a concrete resolution of demonic
choices. A demonic event chooses one branch and takes a silent step. -/
inductive DemonicIrelF {ε : Type u → Type (u + 1)} {ρ : Type*}
    (sim : ITree (DemonicE + ε) ρ → ITree ε ρ → Prop) :
    ITree (DemonicE + ε) ρ → ITree ε ρ → Prop where
  | choose (α : Type u) (default x : α)
      (k : α → ITree (DemonicE + ε) ρ) (t : ITree ε ρ)
      (h : sim (k x) t) :
      DemonicIrelF sim (vis (SumE.inl (.choose α default)) k) (tau t)
  | ret (x : ρ) : DemonicIrelF sim (ret x) (ret x)
  | tau (t : ITree (DemonicE + ε) ρ) (t' : ITree ε ρ) (h : sim t t') :
      DemonicIrelF sim (tau t) (tau t')
  | vis {α : Type u} (e : ε α)
      (k : α → ITree (DemonicE + ε) ρ) (k' : α → ITree ε ρ)
      (h : ∀ x, sim (k x) (k' x)) :
      DemonicIrelF sim (vis (SumE.inr e) k) (vis e k')

theorem DemonicIrelF_monotone {ε : Type u → Type (u + 1)} {ρ : Type*}
    {sim sim' : ITree (DemonicE + ε) ρ → ITree ε ρ → Prop}
    (hmono : ∀ t t', sim t t' → sim' t t') :
    ∀ {t t'}, DemonicIrelF sim t t' → DemonicIrelF sim' t t' := by
  intro t t' h
  cases h with
  | choose α default x k t h => exact .choose α default x k t (hmono _ _ h)
  | ret x => exact .ret x
  | tau t t' h => exact .tau t t' (hmono _ _ h)
  | vis e k k' h => exact .vis e k k' (fun x => hmono _ _ (h x))

def DemonicIrelOp {ε : Type u → Type (u + 1)} {ρ : Type*}
    (sim : ITree (DemonicE + ε) ρ → ITree ε ρ →
      Lean.Order.ReverseImplicationOrder) :
    ITree (DemonicE + ε) ρ → ITree ε ρ →
      Lean.Order.ReverseImplicationOrder :=
  fun t t' => DemonicIrelF sim t t'

theorem DemonicIrelOp_monotone {ε : Type u → Type (u + 1)} {ρ : Type*} :
    Lean.Order.monotone (@DemonicIrelOp ε ρ) := by
  intro sim sim' hsim t t' h
  exact DemonicIrelF_monotone (fun a b => hsim a b) h

/-- A concrete tree resolves every demonic event of the source tree. -/
noncomputable def DemonicIrel {ε : Type u → Type (u + 1)} {ρ : Type*}
    (t : ITree (DemonicE + ε) ρ) (t' : ITree ε ρ) : Prop :=
  ITree.reverseToProp
    (Lean.Order.lfp_monotone (@DemonicIrelOp ε ρ)
      DemonicIrelOp_monotone t t')

theorem DemonicIrel_unfold {ε : Type u → Type (u + 1)} {ρ : Type*}
    (t : ITree (DemonicE + ε) ρ) (t' : ITree ε ρ) :
    DemonicIrel t t' ↔ DemonicIrelF DemonicIrel t t' := by
  unfold DemonicIrel ITree.reverseToProp
  delta Lean.Order.lfp_monotone
  conv_lhs => rw [Lean.Order.lfp_fix DemonicIrelOp_monotone]
  rfl

theorem DemonicIrel_coinduct {ε : Type u → Type (u + 1)} {ρ : Type*}
    (R : ITree (DemonicE + ε) ρ → ITree ε ρ → Prop)
    (hstep : ∀ t t', R t t' → DemonicIrelF R t t') :
    ∀ t t', R t t' → DemonicIrel t t' := by
  have hpost : Lean.Order.PartialOrder.rel
      (@DemonicIrelOp ε ρ
        (fun t t' => (R t t' : Lean.Order.ReverseImplicationOrder)))
      (fun t t' => (R t t' : Lean.Order.ReverseImplicationOrder)) := by
    change ∀ t t', R t t' → DemonicIrelF R t t'
    exact hstep
  have hlfp := Lean.Order.lfp_le_of_le hpost
  intro t t' h
  unfold DemonicIrel ITree.reverseToProp
  exact hlfp t t' h

/-- Resolve every demonic choice using the default value stored in its event. -/
def demonicIfn {ε : Type u → Type (u + 1)} {ρ : Type*}
    (t : ITree (DemonicE + ε) ρ) : ITree ε ρ :=
  .corecEmbed (fun t =>
    match t.dest with
    | ⟨.ret x, _⟩ => .inl (ret x)
    | ⟨.tau, c⟩ => .inr (tau' (.inr (c 0)))
    | ⟨.vis α (.inl e), k⟩ =>
        match e with
        | .choose _ default => .inr (tau' (.inr (k default)))
    | ⟨.vis _ (.inr e), k⟩ => .inr (vis' e (fun x => .inr (k x)))) t

@[simp]
theorem demonicIfn_ret {ε : Type u → Type (u + 1)} {ρ : Type*} (x : ρ) :
    demonicIfn (ε := ε) (ret x) = ret x := by
  conv => lhs; simp only [demonicIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem demonicIfn_tau {ε : Type u → Type (u + 1)} {ρ : Type*}
    (t : ITree (DemonicE + ε) ρ) :
    demonicIfn (tau t) = tau (demonicIfn t) := by
  conv => lhs; simp only [demonicIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem demonicIfn_choose {ε : Type u → Type (u + 1)} {ρ : Type*}
    {α : Type u} (default : α) (k : α → ITree (DemonicE + ε) ρ) :
    demonicIfn (vis (SumE.inl (.choose α default)) k) =
      tau (demonicIfn (k default)) := by
  conv => lhs; simp only [demonicIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem demonicIfn_vis {ε : Type u → Type (u + 1)} {ρ : Type*}
    {α : Type u} (e : ε α) (k : α → ITree (DemonicE + ε) ρ) :
    demonicIfn (vis (SumE.inr e) k) = vis e (fun x => demonicIfn (k x)) := by
  conv => lhs; simp only [demonicIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

theorem demonicIfn_irel {ε : Type u → Type (u + 1)} {ρ : Type*}
    (t : ITree (DemonicE + ε) ρ) : DemonicIrel t (demonicIfn t) := by
  apply DemonicIrel_coinduct (fun s t' => t' = demonicIfn s)
  · intro s t' h
    subst t'
    apply s.dMatchOn
    · intro x hx
      rw [hx, demonicIfn_ret]
      exact .ret x
    · intro next hnext
      rw [hnext, demonicIfn_tau]
      exact .tau next _ rfl
    · intro α e k hk
      rw [hk]
      cases e with
      | inl choice =>
          cases choice with
          | choose default =>
              rw [demonicIfn_choose]
              exact .choose α default default k _ rfl
      | inr e =>
          rw [demonicIfn_vis]
          exact .vis e k _ (fun _ => rfl)
  · exact rfl

end ProgramLogicCarte
