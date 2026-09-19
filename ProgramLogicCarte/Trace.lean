import ITree.Translate
import ITree.UpToTaus

/-!
# Finite interaction-tree traces

This ports the foundational part of `src/trace.v`. A trace records visible
events and their answers, ignores silent steps, and may stop early at `cut`.
-/

namespace ProgramLogicCarte

open ITree

universe u v uₑ

inductive Trace (ε : Type u → Type v) (ρ : Type uₑ) where
  | ret (x : ρ)
  | vis {α : Type u} (e : ε α) (answer : α) (next : Trace ε ρ)
  | visEmpty {α : Type u} (e : ε α)
  | cut

namespace Trace

/-- `IsTrace tr t` states that `tr` is one finite execution path through `t`.
The `visEmpty` case carries evidence that the event has no possible answer. -/
inductive IsTrace {ε : Type u → Type v} {ρ : Type uₑ} :
    Trace ε ρ → ITree ε ρ → Prop where
  | ret (x : ρ) : IsTrace (.ret x) (ITree.ret x)
  | vis {α : Type u} (e : ε α) (answer : α)
      (k : α → ITree ε ρ) (tr : Trace ε ρ)
      (h : IsTrace tr (k answer)) :
      IsTrace (.vis e answer tr) (ITree.vis e k)
  | visEmpty {α : Type u} (e : ε α) (k : α → ITree ε ρ)
      (empty : α → False) :
      IsTrace (.visEmpty e) (ITree.vis e k)
  | cut (t : ITree ε ρ) : IsTrace .cut t
  | tau {tr : Trace ε ρ} {t : ITree ε ρ} (h : IsTrace tr t) :
      IsTrace tr (ITree.tau t)

theorem ret_isTrace (x : ρ) : IsTrace (.ret x) (ITree.ret x : ITree ε ρ) :=
  .ret x

theorem cut_isTrace (t : ITree ε ρ) : IsTrace .cut t :=
  .cut t

theorem vis_isTrace {α : Type u} (e : ε α) (answer : α)
    (k : α → ITree ε ρ) {tr : Trace ε ρ} (h : IsTrace tr (k answer)) :
    IsTrace (.vis e answer tr) (ITree.vis e k) :=
  .vis e answer k tr h

theorem tau_isTrace {tr : Trace ε ρ} {t : ITree ε ρ}
    (h : IsTrace tr t) : IsTrace tr (ITree.tau t) :=
  .tau h

/-- Rename the events recorded by a trace. -/
def translate (f : ε₁ ⟶ ε₂) : Trace ε₁ ρ → Trace ε₂ ρ
  | .ret x => .ret x
  | .vis e answer next => .vis (f e) answer (translate f next)
  | .visEmpty e => .visEmpty (f e)
  | .cut => .cut

/-- Translating an interaction tree translates each of its finite traces. -/
theorem translate_isTrace (f : ε₁ ⟶ ε₂)
    {tr : Trace ε₁ ρ} {t : ITree ε₁ ρ} (h : IsTrace tr t) :
    IsTrace (translate f tr) (ITree.translate f t) := by
  induction h with
  | ret x =>
      change IsTrace (.ret x) (ITree.translate f (ITree.ret x))
      rw [ITree.translate_ret]
      exact .ret x
  | vis e answer k tr _ ih =>
      rw [ITree.translate_vis]
      exact .vis (f e) answer _ _ ih
  | visEmpty e k empty =>
      rw [ITree.translate_vis]
      exact .visEmpty (f e) _ empty
  | cut t => exact .cut _
  | tau h ih =>
      rw [ITree.translate_tau]
      exact .tau ih

/-- Remove all events in the left summand from a trace, retaining events in
the right summand. A left event with no answer becomes a cut. -/
def eraseLeft : Trace (ε₁ + ε₂) ρ → Trace ε₂ ρ
  | .ret x => .ret x
  | .vis (.inl _) _ next => eraseLeft next
  | .vis (.inr e) answer next => .vis e answer (eraseLeft next)
  | .visEmpty (.inl _) => .cut
  | .visEmpty (.inr e) => .visEmpty e
  | .cut => .cut

/-- A terminating trace determines weak equivalence with the corresponding
return tree. -/
theorem ret_eutt {x : ρ} {t : ITree ε ρ} (h : IsTrace (.ret x) t) :
    IEqutt t (ITree.ret x) := by
  generalize htr : (Trace.ret x : Trace ε ρ) = tr at h
  induction h generalizing x with
  | ret y =>
      cases htr
      exact iequtt_refl _
  | vis e answer k tr h ih => cases htr
  | visEmpty e k empty => cases htr
  | cut t => cases htr
  | tau h ih => exact iequtt_tau_left (ih htr)

end Trace

end ProgramLogicCarte
