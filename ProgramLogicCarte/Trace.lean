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

/-- A prefix may stop at `cut`, or retain the same event and answer and
continue with a prefix of the tail. Returns and unanswered empty events are
terminal: they can only prefix themselves. Using an indexed relation keeps
each event and answer at the same dependent response type. -/
inductive IsPrefix {ε : Type u → Type v} {ρ : Type uₑ} :
    Trace ε ρ → Trace ε ρ → Prop where
  | cut (tr : Trace ε ρ) : IsPrefix .cut tr
  | ret (x : ρ) : IsPrefix (.ret x) (.ret x)
  | vis {α : Type u} (e : ε α) (answer : α)
      {pre tr : Trace ε ρ} (tail : IsPrefix pre tr) :
      IsPrefix (.vis e answer pre) (.vis e answer tr)
  | visEmpty {α : Type u} (e : ε α) : IsPrefix (.visEmpty e) (.visEmpty e)


namespace IsPrefix

theorem refl (tr : Trace ε ρ) : IsPrefix tr tr := by
  induction tr with
  | ret x => exact .ret x
  | vis e answer next ih => exact .vis e answer ih
  | visEmpty e => exact .visEmpty e
  | cut => exact .cut _

theorem trans {first middle last : Trace ε ρ}
    (h₁ : IsPrefix first middle) (h₂ : IsPrefix middle last) : IsPrefix first last := by
  induction h₁ generalizing last with
  | cut tr => exact .cut _
  | ret x => cases h₂; exact .ret x
  | vis e answer tail ih =>
      cases h₂ with
      | vis _ _ rest => exact .vis e answer (ih rest)
  | visEmpty e => cases h₂; exact .visEmpty e

theorem antisymm {first second : Trace ε ρ}
    (h₁ : IsPrefix first second) (h₂ : IsPrefix second first) : first = second := by
  induction h₁ with
  | cut tr => cases h₂; rfl
  | ret x => rfl
  | vis e answer tail ih =>
      cases h₂ with
      | vis _ _ rest => exact congrArg (Trace.vis e answer) (ih rest)
  | visEmpty e => rfl

/-- Every prefix of an execution trace is also an execution trace. -/
theorem isTrace {pre tr : Trace ε ρ} {t : ITree ε ρ}
    (hp : IsPrefix pre tr) (ht : IsTrace tr t) : IsTrace pre t := by
  induction ht generalizing pre with
  | ret x =>
      cases hp with
      | cut => exact .cut _
      | ret => exact .ret x
  | vis e answer k tr h ih =>
      cases hp with
      | cut => exact .cut _
      | vis _ _ tail => exact .vis e answer k _ (ih tail)
  | visEmpty e k empty =>
      cases hp with
      | cut => exact .cut _
      | visEmpty => exact .visEmpty e k empty
  | cut t => cases hp; exact .cut _
  | tau h ih => exact .tau (ih hp)

theorem translate (f : ε₁ ⟶ ε₂) {pre tr : Trace ε₁ ρ}
    (h : IsPrefix pre tr) : IsPrefix (Trace.translate f pre) (Trace.translate f tr) := by
  induction h with
  | cut tr => exact .cut _
  | ret x => exact .ret x
  | vis e answer tail ih => exact .vis (f e) answer ih
  | visEmpty e => exact .visEmpty (f e)

theorem eraseLeft {pre tr : Trace (ε₁ + ε₂) ρ} (h : IsPrefix pre tr) :
    IsPrefix (Trace.eraseLeft pre) (Trace.eraseLeft tr) := by
  induction h with
  | cut tr => exact .cut _
  | ret x => exact .ret x
  | vis e answer tail ih =>
      cases e with
      | inl e => exact ih
      | inr e => exact .vis e answer ih
  | visEmpty e =>
      cases e with
      | inl e => exact .cut _
      | inr e => exact .visEmpty e

end IsPrefix

@[simp] theorem cut_isPrefix (tr : Trace ε ρ) : IsPrefix .cut tr := .cut tr

@[simp] theorem isPrefix_self (tr : Trace ε ρ) : IsPrefix tr tr := .refl tr

@[simp] theorem isPrefix_cut_iff {tr : Trace ε ρ} : IsPrefix tr .cut ↔ tr = .cut := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .cut _

@[simp] theorem ret_isPrefix_iff {x : ρ} {tr : Trace ε ρ} :
    IsPrefix (.ret x) tr ↔ tr = .ret x := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .ret x

@[simp] theorem visEmpty_isPrefix_iff {α : Type u} {e : ε α} {tr : Trace ε ρ} :
    IsPrefix (.visEmpty e) tr ↔ tr = .visEmpty e := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .visEmpty e

@[simp] theorem vis_isPrefix_vis_iff {α : Type u} {e : ε α} {answer : α}
    {pre tr : Trace ε ρ} :
    IsPrefix (.vis e answer pre) (.vis e answer tr) ↔ IsPrefix pre tr := by
  constructor
  · intro h
    cases h with
    | vis _ _ tail => exact tail
  · exact .vis e answer

end Trace

end ProgramLogicCarte
