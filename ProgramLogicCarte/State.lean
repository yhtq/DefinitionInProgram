import ProgramLogicCarte.Wpi
import ITree.UpToTaus

/-! Stateful effects and their relational/functional interpretation (`src/state.v`). -/

namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE ITree

universe u uₑ

/-- Stateful events. The unit answer is lifted so both constructors live in
the same universe-polymorphic signature. -/
inductive StateE (S : Type u) : Type u → Type u where
  | get : StateE S S
  | set (value : S) : StateE S (ULift Unit)

def getState {S : Type u} {ε : Type u → Type u} (inject : StateE S ⟶ ε) :
    ITree ε S :=
  trigger (inject .get)

def setState {S : Type u} {ε : Type u → Type u} (inject : StateE S ⟶ ε)
    (value : S) : ITree ε (ULift Unit) :=
  trigger (inject (.set value))

/-- Iris assertion describing ownership of the current external state. -/
class StateInterp (GF : BundledGFunctors) (S : Type u) where
  interp : S → IProp GF

export StateInterp (interp)

/-- The assertion assigned to one state event.  Kept separate from the
`IHandler` package so dependent pattern matching reduces transparently in the
handler laws. -/
def stateHandle {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {S : Type u} [StateInterp GF S] {α : Type u} (e : StateE S α)
    (Φ : α → IProp GF) : IProp GF :=
  match e with
  | .get => iprop(∀ s,
      interp (GF := GF) (S := S) s ={∅}=∗
        interp (GF := GF) (S := S) s ∗ Φ s)
  | .set next => iprop(∀ s,
      interp (GF := GF) (S := S) s ={∅}=∗
        interp (GF := GF) (S := S) next ∗ Φ (.up ()))

/-- Logical handler for state operations.  Every operation temporarily takes
ownership of the current state and returns ownership of the resulting state. -/
def stateH {GF : BundledGFunctors} [InvGS_gen hlc GF]
    (S : Type u) [StateInterp GF S] : IHandler GF (StateE S) where
  handle e Φ _ := stateHandle (GF := GF) (S := S) e Φ
  mono e := by
    cases e with
    | get =>
        intro Φ Φ' spawned spawned'
        simp only [stateHandle]
        istart
        iintro HΦ _ Hget
        iintro %s Hs
        imod Hget $$ Hs with ⟨Hs, Hpost⟩
        imodintro
        iframe Hs
        iapply HΦ $$ Hpost
    | set next =>
        intro Φ Φ' spawned spawned'
        simp only [stateHandle]
        istart
        iintro HΦ _ Hset
        iintro %s Hs
        imod Hset $$ Hs with ⟨Hs, Hpost⟩
        imodintro
        iframe Hs
        iapply HΦ $$ Hpost
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    cases e with
    | get =>
        simp only [stateHandle]
        exact forall_ne fun s => wand_ne.ne .rfl <|
          BIFUpdate.ne.ne <| sep_ne.ne .rfl (hΦ s)
    | set next =>
        simp only [stateHandle]
        exact forall_ne fun s => wand_ne.ne .rfl <|
          BIFUpdate.ne.ne <| sep_ne.ne .rfl (hΦ (.up ()))

instance stateHSequential {GF : BundledGFunctors} [InvGS_gen hlc GF]
    (S : Type u) [StateInterp GF S] :
    IHandler.Sequential (stateH (GF := GF) S) where
  sequential e Φ spawned := by
    cases e <;> exact .rfl

/-- Empty-mask WP rule for reading the state through the direct handler. -/
theorem wpi_getState {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {S : Type u} [StateInterp GF S] (Φ : S → IProp GF) :
    iprop(∀ s, interp (GF := GF) (S := S) s ={∅}=∗
      interp (GF := GF) (S := S) s ∗ Φ s) ⊢
      wpi (stateH S) (getState (fun e => e)) Φ := by
  rw [getState, trigger, wpi_vis]
  istart
  iintro Hget
  imodintro
  isimp only [stateH, stateHandle]
  iintro %s Hs
  imod Hget $$ Hs with ⟨Hs, Hpost⟩
  imodintro
  iframe Hs
  rw [wpi_ret]
  imodintro
  iexact Hpost

/-- Empty-mask WP rule for replacing the state through the direct handler. -/
theorem wpi_setState {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {S : Type u} [StateInterp GF S] (next : S)
    (Φ : ULift Unit → IProp GF) :
    iprop(∀ s, interp (GF := GF) (S := S) s ={∅}=∗
      interp (GF := GF) (S := S) next ∗ Φ (.up ())) ⊢
      wpi (stateH S) (setState (fun e => e) next) Φ := by
  rw [setState, trigger, wpi_vis]
  istart
  iintro Hset
  imodintro
  isimp only [stateH, stateHandle]
  iintro %s Hs
  imod Hset $$ Hs with ⟨Hs, Hpost⟩
  imodintro
  iframe Hs
  rw [wpi_ret]
  imodintro
  iexact Hpost

/-- One observable layer of the state interpretation relation. -/
inductive StateIrelF {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (sim : S → ITree (StateE S + ε) ρ → ITree ε (S × ρ) → Prop) :
    S → ITree (StateE S + ε) ρ → ITree ε (S × ρ) → Prop where
  | ret (state : S) (x : ρ) :
      StateIrelF sim state (ret x) (ret (state, x))
  | tau (state : S) (t : ITree (StateE S + ε) ρ)
      (t' : ITree ε (S × ρ)) (h : sim state t t') :
      StateIrelF sim state (tau t) (tau t')
  | vis (state : S) {α : Type u} (e : ε α)
      (k : α → ITree (StateE S + ε) ρ) (k' : α → ITree ε (S × ρ))
      (h : ∀ x, sim state (k x) (k' x)) :
      StateIrelF sim state (vis (SumE.inr e) k) (vis e k')
  | get (state : S) (k : S → ITree (StateE S + ε) ρ)
      (t : ITree ε (S × ρ)) (h : sim state (k state) t) :
      StateIrelF sim state (vis (SumE.inl StateE.get) k) (tau t)
  | set (state next : S)
      (k : ULift Unit → ITree (StateE S + ε) ρ)
      (t : ITree ε (S × ρ)) (h : sim next (k (.up ())) t) :
      StateIrelF sim state (vis (SumE.inl (.set next)) k) (tau t)

theorem StateIrelF_monotone {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    {sim sim' : S → ITree (StateE S + ε) ρ → ITree ε (S × ρ) → Prop}
    (hmono : ∀ s t t', sim s t t' → sim' s t t') :
    ∀ {s t t'}, StateIrelF sim s t t' → StateIrelF sim' s t t' := by
  intro s t t' h
  cases h with
  | ret x => exact .ret s x
  | tau t t' h => exact .tau s t t' (hmono _ _ _ h)
  | vis e k k' h => exact .vis s e k k' (fun x => hmono _ _ _ (h x))
  | get k t h => exact .get s k t (hmono _ _ _ h)
  | set next k t h => exact .set s next k t (hmono _ _ _ h)

def StateIrelOp {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (sim : S → ITree (StateE S + ε) ρ → ITree ε (S × ρ) →
      Lean.Order.ReverseImplicationOrder) :
    S → ITree (StateE S + ε) ρ → ITree ε (S × ρ) →
      Lean.Order.ReverseImplicationOrder :=
  fun s t t' => StateIrelF sim s t t'

theorem StateIrelOp_monotone {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ} :
    Lean.Order.monotone (@StateIrelOp S ε ρ) := by
  intro sim sim' hsim s t t' h
  exact StateIrelF_monotone (fun a b c => hsim a b c) h

noncomputable def StateIrel {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (state : S) (t : ITree (StateE S + ε) ρ) (t' : ITree ε (S × ρ)) : Prop :=
  reverseToProp
    (Lean.Order.lfp_monotone (@StateIrelOp S ε ρ) StateIrelOp_monotone state t t')

theorem StateIrel_unfold {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (state : S) (t : ITree (StateE S + ε) ρ) (t' : ITree ε (S × ρ)) :
    StateIrel state t t' ↔ StateIrelF StateIrel state t t' := by
  unfold StateIrel reverseToProp
  delta Lean.Order.lfp_monotone
  conv_lhs => rw [Lean.Order.lfp_fix StateIrelOp_monotone]
  rfl

theorem StateIrel_coinduct {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (R : S → ITree (StateE S + ε) ρ → ITree ε (S × ρ) → Prop)
    (hstep : ∀ s t t', R s t t' → StateIrelF R s t t') :
    ∀ s t t', R s t t' → StateIrel s t t' := by
  have hpost : Lean.Order.PartialOrder.rel
      (@StateIrelOp S ε ρ
        (fun s t t' => (R s t t' : Lean.Order.ReverseImplicationOrder)))
      (fun s t t' => (R s t t' : Lean.Order.ReverseImplicationOrder)) := by
    change ∀ s t t', R s t t' → StateIrelF R s t t'
    exact hstep
  have hlfp := Lean.Order.lfp_le_of_le hpost
  intro s t t' h
  unfold StateIrel reverseToProp
  exact hlfp s t t' h

/-- Execute state events, threading the current state and returning the final
state together with the source return value. -/
def stateIfn {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (initial : S) (t : ITree (StateE S + ε) ρ) : ITree ε (S × ρ) :=
  .corecEmbed (fun (st : S × ITree (StateE S + ε) ρ) =>
    let (state, t) := st
    match t.dest with
    | ⟨.ret x, _⟩ => .inl (ret (state, x))
    | ⟨.tau, c⟩ => .inr (tau' (.inr (state, c 0)))
    | ⟨.vis _ (.inl .get), k⟩ => .inr (tau' (.inr (state, k state)))
    | ⟨.vis _ (.inl (.set next)), k⟩ => .inr (tau' (.inr (next, k (.up ()))))
    | ⟨.vis _ (.inr e), k⟩ => .inr (vis' e (fun x => .inr (state, k x))))
    (initial, t)

@[simp]
theorem stateIfn_ret {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (state : S) (x : ρ) : stateIfn (ε := ε) state (ret x) = ret (state, x) := by
  conv => lhs; simp only [stateIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem stateIfn_tau {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (state : S) (t : ITree (StateE S + ε) ρ) :
    stateIfn state (tau t) = tau (stateIfn state t) := by
  conv => lhs; simp only [stateIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem stateIfn_get {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (state : S) (k : S → ITree (StateE S + ε) ρ) :
    stateIfn state (vis (SumE.inl StateE.get) k) = tau (stateIfn state (k state)) := by
  conv => lhs; simp only [stateIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem stateIfn_set {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (state next : S) (k : ULift Unit → ITree (StateE S + ε) ρ) :
    stateIfn state (vis (SumE.inl (.set next)) k) =
      tau (stateIfn next (k (.up ()))) := by
  conv => lhs; simp only [stateIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem stateIfn_vis {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (state : S) {α : Type u} (e : ε α) (k : α → ITree (StateE S + ε) ρ) :
    stateIfn state (vis (SumE.inr e) k) = vis e (fun x => stateIfn state (k x)) := by
  conv => lhs; simp only [stateIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

theorem stateIfn_irel {S : Type u} {ε : Type u → Type u} {ρ : Type uₑ}
    (state : S) (t : ITree (StateE S + ε) ρ) :
    StateIrel state t (stateIfn state t) := by
  apply StateIrel_coinduct (fun s source out => out = stateIfn s source)
  · intro s source out h
    subst out
    apply source.dMatchOn
    · intro x hx
      rw [hx, stateIfn_ret]
      exact .ret s x
    · intro next hnext
      rw [hnext, stateIfn_tau]
      exact .tau s next _ rfl
    · intro α e k hk
      rw [hk]
      cases e with
      | inl stateEvent =>
          cases stateEvent with
          | get =>
              rw [stateIfn_get]
              exact .get s k _ rfl
          | set next =>
              rw [stateIfn_set]
              exact .set s next k _ rfl
      | inr e =>
          rw [stateIfn_vis]
          exact .vis s e k _ (fun _ => rfl)
  · exact rfl

end ProgramLogicCarte
