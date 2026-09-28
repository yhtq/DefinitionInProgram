import Iris.ProofMode
import ITree.EffectAlgebra

/-!
# Logical effect handlers

This is the Lean counterpart of `src/handler.v`. A handler assigns a BI
proposition to each event, parameterized by the ordinary continuation and the
continuation used when the event spawns a thread.
-/

namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE

universe u v₁ v₂ w

/-- A logical interpretation of an effect signature. -/
structure IHandlerBase (PROP : Type w) [BI PROP] (ε : Type u → Type v₁) where
  handle {α : Type u} (e : ε α)
    (continuation spawned : α → PROP) : PROP
  mono : ∀ {α : Type u} (e : ε α) Φ Φ' spawned spawned', (⊢ iprop(
    (∀ x, Φ x -∗ Φ' x) -∗
    □ (∀ x, spawned x -∗ spawned' x) -∗
    handle e Φ spawned -∗ handle e Φ' spawned'))
  ne : ∀ {n} {α : Type u} (e : ε α) {Φ₁ Φ₂ spawned₁ spawned₂ : α → PROP},
    (∀ x, Φ₁ x ≡{n}≡ Φ₂ x) →
    (∀ x, spawned₁ x ≡{n}≡ spawned₂ x) →
    handle e Φ₁ spawned₁ ≡{n}≡ handle e Φ₂ spawned₂

namespace IHandler

variable {PROP : Type w} [BI PROP]
  {ε₁ : Type u → Type v₁} {ε₂ : Type u → Type v₁}

/-- Delegate events of a sum to their respective logical handlers. -/
def sum (H₁ : IHandlerBase PROP ε₁) (H₂ : IHandlerBase PROP ε₂) :
    IHandlerBase PROP (ε₁ + ε₂) where
  handle e := match e with
    | .inl e₁ => H₁.handle e₁
    | .inr e₂ => H₂.handle e₂
  mono e := by
    cases e with
    | inl e₁ => exact H₁.mono e₁
    | inr e₂ => exact H₂.mono e₂
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    cases e with
    | inl e₁ => exact H₁.ne e₁ hΦ hspawned
    | inr e₂ => exact H₂.ne e₂ hΦ hspawned

infixr:55 " ⊕ₕ " => sum

/-- `Small` agrees with `Big` on events embedded by `inject`. -/
class Includes (inject : ε₁ ⟶ ε₂)
    (Small : IHandlerBase PROP ε₁) (Big : IHandlerBase PROP ε₂) : Prop where
  equiv : ∀ {α : Type u} (e : ε₁ α) Φ spawned,
    Big.handle (inject e) Φ spawned ⊣⊢ Small.handle e Φ spawned

instance includesRefl (H : IHandlerBase PROP ε₁) :
    Includes (fun e => e) H H where
  equiv := fun _ _ _ => .rfl

instance includesSumLeft (H₁ : IHandlerBase PROP ε₁) (H₂ : IHandlerBase PROP ε₂) :
    Includes (fun e => SumE.inl e) H₁ (H₁ ⊕ₕ H₂) where
  equiv := fun _ _ _ => .rfl

instance includesSumRight (H₁ : IHandlerBase PROP ε₁) (H₂ : IHandlerBase PROP ε₂) :
    Includes (fun e => SumE.inr e) H₂ (H₁ ⊕ₕ H₂) where
  equiv := fun _ _ _ => .rfl

/-- Pointwise logical implication between handlers over one signature. -/
class Entails (H₁ H₂ : IHandlerBase PROP ε₁) : Prop where
  entails : ∀ {α : Type u} (e : ε₁ α) Φ spawned,
    H₁.handle e Φ spawned ⊢ H₂.handle e Φ spawned

instance entailsRefl (H : IHandlerBase PROP ε₁) : Entails H H where
  entails := fun _ _ _ => .rfl

instance entailsSum {H₁ H₁' : IHandlerBase PROP ε₁}
    {H₂ H₂' : IHandlerBase PROP ε₂} [Entails H₁ H₁'] [Entails H₂ H₂'] :
    Entails (H₁ ⊕ₕ H₂) (H₁' ⊕ₕ H₂') where
  entails e Φ spawned := by
    cases e with
    | inl e₁ => exact Entails.entails e₁ Φ spawned
    | inr e₂ => exact Entails.entails e₂ Φ spawned

/-- Sequential handlers ignore the continuation reserved for newly spawned
threads. -/
class Sequential (H : IHandlerBase PROP ε₁) : Prop where
  sequential : ∀ {α : Type u} (e : ε₁ α) Φ spawned,
    H.handle e Φ spawned ⊢ H.handle e Φ (fun _ => iprop(False))

instance sequentialSum (H₁ : IHandlerBase PROP ε₁) (H₂ : IHandlerBase PROP ε₂)
    [Sequential H₁] [Sequential H₂] : Sequential (H₁ ⊕ₕ H₂) where
  sequential e Φ spawned := by
    cases e with
    | inl e₁ => exact Sequential.sequential e₁ Φ spawned
    | inr e₂ => exact Sequential.sequential e₂ Φ spawned

end IHandler

end ProgramLogicCarte
