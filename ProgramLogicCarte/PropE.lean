import Iris.BI.MonPred

/-! BI propositions indexed by a fresh, abstract symbol. -/
namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE

/-- A proposition depending on an abstract symbol of type `α`. -/
abbrev PropE (α : Type u) (PROP : Type v) := α → PROP

namespace PropE


variable {α : Type u} {PROP : Type v} [BI PROP]

instance : BIBase (PropE α PROP) where
  Entails P Q := ∀ a, P a ⊢ Q a
  emp := fun _ => BIBase.emp
  pure φ := fun _ => BIBase.pure φ
  and P Q := fun a => BIBase.and (P a) (Q a)
  or P Q := fun a => BIBase.or (P a) (Q a)
  imp P Q := fun a => BIBase.imp (P a) (Q a)
  sForall Ψ := fun a => BIBase.sForall (fun p => ∃ Q : PropE α PROP, Ψ Q ∧ Q a = p)
  sExists Ψ := fun a => BIBase.sExists (fun p => ∃ Q : PropE α PROP, Ψ Q ∧ Q a = p)
  sep P Q := fun a => BIBase.sep (P a) (Q a)
  wand P Q := fun a => BIBase.wand (P a) (Q a)
  persistently P := fun a => BIBase.persistently (P a)
  later P := fun a => BIBase.later (P a)

instance : BI (PropE α PROP) where
  entails_refl _ := BIBase.Entails.rfl
  entails_trans h h' a := (h a).trans (h' a)
  equiv_iff := fun {P Q} =>
    ⟨fun h => ⟨fun a => BIBase.Entails.of_eq (congrFun h a),
               fun a => BIBase.Entails.of_eq (congrFun h.symm a)⟩,
     fun h => funext fun a => BI.equiv_iff.mpr ⟨h.1 a, h.2 a⟩⟩
  and_ne := ⟨fun _ _ _ h _ _ h' a => and_ne.ne (h a) (h' a)⟩
  or_ne := ⟨fun _ _ _ h _ _ h' a => or_ne.ne (h a) (h' a)⟩
  imp_ne := ⟨fun _ _ _ h _ _ h' a => imp_ne.ne (h a) (h' a)⟩
  sForall_ne := fun {n Ψ₁ Ψ₂} h a =>
    Iris.BI.sForall_ne
      ⟨fun _ ⟨q, hq, hp⟩ =>
          let ⟨q', hq', hr⟩ := h.1 q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ hr a⟩,
       fun _ ⟨q, hq, hp⟩ =>
          let ⟨q', hq', hr⟩ := h.2 q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ hr a⟩⟩
  sExists_ne := fun {n Ψ₁ Ψ₂} h a =>
    Iris.BI.sExists_ne
      ⟨fun _ ⟨q, hq, hp⟩ =>
          let ⟨q', hq', hr⟩ := h.1 q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ hr a⟩,
       fun _ ⟨q, hq, hp⟩ =>
          let ⟨q', hq', hr⟩ := h.2 q hq; ⟨_, ⟨q', hq', rfl⟩, hp ▸ hr a⟩⟩
  sep_ne := ⟨fun _ _ _ h _ _ h' a => sep_ne.ne (h a) (h' a)⟩
  wand_ne := ⟨fun _ _ _ h _ _ h' a => wand_ne.ne (h a) (h' a)⟩
  persistently_ne := ⟨fun _ _ _ h a => persistently_ne.ne (h a)⟩
  later_ne := ⟨fun _ _ _ h a => later_ne.ne (h a)⟩
  pure_intro h _ := pure_intro h
  pure_elim' h a := pure_elim' fun hp => h hp a
  and_elim_l _ := and_elim_l
  and_elim_r _ := and_elim_r
  and_intro h h' a := and_intro (h a) (h' a)
  or_intro_l _ := or_intro_l
  or_intro_r _ := or_intro_r
  or_elim h h' a := or_elim (h a) (h' a)
  imp_intro h a := imp_intro (h a)
  imp_elim h a := imp_elim (h a)
  sForall_intro h a := sForall_intro fun p ⟨q, hq, hp⟩ => by
    subst p
    exact h q hq a
  sForall_elim h a := sForall_elim ⟨_, h, rfl⟩
  sExists_intro h a := sExists_intro ⟨_, h, rfl⟩
  sExists_elim h a := sExists_elim fun p ⟨q, hq, hp⟩ => by
    subst p
    exact h q hq a
  sep_mono h h' a := sep_mono (h a) (h' a)
  emp_sep := ⟨fun _ => emp_sep.mp, fun _ => emp_sep.mpr⟩
  sep_symm _ := sep_symm
  sep_assoc_l _ := sep_assoc_l
  wand_intro h a := wand_intro (h a)
  wand_elim h a := wand_elim (h a)
  persistently_mono h a := persistently_mono (h a)
  persistently_idem_2 _ := persistently_idem_2
  persistently_emp_2 _ := persistently_emp_2
  persistently_and_2 _ := persistently_and_2
  persistently_absorb_l _ := persistently_absorb_l
  persistently_and_l _ := persistently_and_l
  later_mono h a := later_mono (h a)
  later_intro _ := later_intro
  later_sForall_2 := fun {Φ} a => by
    refine .trans ?_ later_sForall_2
    refine sForall_intro fun p hp => ?_
    rcases hp with ⟨q, hq⟩
    subst p
    refine imp_intro <| pure_elim_right ?_
    rintro ⟨r, hΦ, hr⟩
    subst q
    exact (sForall_elim ⟨_, ⟨r, rfl⟩, rfl⟩).trans (pure_imp_elim hΦ)
  later_sExists_false := fun {Φ} a => by
    refine later_sExists_false.trans (or_mono_right ?_)
    refine exists_elim fun p => pure_elim_left fun ⟨q, hΦ, hq⟩ => ?_
    subst hq
    exact (and_intro (pure_intro hΦ) BIBase.Entails.rfl).trans
      (sExists_intro ⟨_, ⟨q, rfl⟩, rfl⟩)
  later_sep := ⟨fun _ => later_sep.mp, fun _ => later_sep.mpr⟩
  later_persistently := ⟨fun _ => later_persistently.mp, fun _ => later_persistently.mpr⟩
  later_false_em := fun {P} a => later_false_em

/-- Embed a base BI proposition without depending on the abstract symbol. -/
def lift (P : PROP) : PropE α PROP := fun _ => P

/-- Entailment in `PropE` means entailment for every symbol value. -/
theorem entails_iff (P Q : PropE α PROP) :
    (P ⊢ Q) ↔ ∀ a, P a ⊢ Q a := Iff.rfl

/-- For an inhabited symbol type, the constant embedding reflects entailment. -/
theorem lift_entails_iff [Inhabited α] (P Q : PROP) :
    (lift (α := α) P ⊢ lift (α := α) Q) ↔ (P ⊢ Q) :=
  ⟨fun h => h default, fun h _ => h⟩

end PropE
end ProgramLogicCarte
