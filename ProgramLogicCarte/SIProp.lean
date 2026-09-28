import ProgramLogicCarte.Wpi

/-! Lower powerdomain of BI propositions. -/
namespace Skolemization

open Iris Iris.BI Iris.OFE ProgramLogicCarte

/-- Downward-closed sets under BI entailment. -/
structure SIProp (PROP : Type w) [BI PROP] where
  carrier : Set (PROP)
  down_closed : ∀ {P Q : PROP}, P ∈ carrier → (Q ⊢ P) → Q ∈ carrier

namespace SIProp

variable {PROP : Type w} [BI PROP]

@[ext] theorem ext {S T : SIProp PROP} (h : S.carrier = T.carrier) : S = T := by
  cases S
  cases T
  cases h
  rfl

instance : COFE (SIProp PROP) := COFE.ofDiscrete _

/-- Downward closure under BI entailment. -/
def down (A : Set (PROP)) : SIProp PROP where
  carrier := {R | ∃ P ∈ A, R ⊢ P}
  down_closed := by
    intro P Q ⟨R, hR, hPR⟩ hQP
    exact ⟨R, hR, hQP.trans hPR⟩

/-- The Hoare relation on sets, equivalent to inclusion on downsets. -/
def HoareEntails (S T : SIProp PROP) : Prop :=
  ∀ P ∈ S.carrier, ∃ Q ∈ T.carrier, P ⊢ Q

theorem hoareEntails_iff_subset (S T : SIProp PROP) :
    HoareEntails S T ↔ S.carrier ⊆ T.carrier := by
  constructor
  · intro h P hP
    obtain ⟨Q, hQ, hPQ⟩ := h P hP
    exact T.down_closed hQ hPQ
  · intro h P hP
    exact ⟨P, h hP, BIBase.Entails.rfl⟩

/-- Embed one BI proposition as a principal downset. -/
abbrev lift (P : PROP) : SIProp PROP := down {P}

@[simp] theorem mem_down_singleton {P Q : PROP} :
    Q ∈ (down ({P} : Set (PROP))).carrier ↔ (Q ⊢ P) := by
  simp [down]

@[simp] theorem mem_down {P : PROP} {A : Set (PROP)} :
    P ∈ (down A).carrier ↔ ∃ Q ∈ A, P ⊢ Q := by
  simp [down]

theorem lift_entails_iff (P Q : PROP) :
    HoareEntails (lift P) (lift Q) ↔ (P ⊢ Q) := by
  rw [hoareEntails_iff_subset]
  constructor
  · intro h
    exact mem_down_singleton.mp (h (mem_down_singleton.mpr BIBase.Entails.rfl))
  · intro h R hR
    exact mem_down_singleton.mpr ((mem_down_singleton.mp hR).trans h)

/-- The requested choice law for a pair of generators. -/
theorem down_pair_entails_iff (P₁ P₂ Q : PROP) :
    HoareEntails (down {P₁, P₂}) (down {Q}) ↔ (P₁ ⊢ Q) ∧ (P₂ ⊢ Q) := by
  rw [hoareEntails_iff_subset]
  constructor
  · intro h
    constructor
    · exact (mem_down_singleton.mp (h (by exact ⟨P₁, by simp, BIBase.Entails.rfl⟩)))
    · exact (mem_down_singleton.mp (h (by exact ⟨P₂, by simp, BIBase.Entails.rfl⟩)))
  · rintro ⟨h₁, h₂⟩ R ⟨P, hP, hRP⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl
    · exact mem_down_singleton.mpr (hRP.trans h₁)
    · exact mem_down_singleton.mpr (hRP.trans h₂)

instance : BIBase (SIProp PROP) where
  Entails S T := S.carrier ⊆ T.carrier
  emp := down {BIBase.emp}
  pure φ := ⟨{P : PROP | φ}, by intro _ _ h _; exact h⟩
  and S T := ⟨S.carrier ∩ T.carrier, by
    intro _ _ h h'; exact ⟨S.down_closed h.1 h', T.down_closed h.2 h'⟩⟩
  or S T := ⟨S.carrier ∪ T.carrier, by
    intro _ _ h h'; rcases h with h | h
    · exact Or.inl (S.down_closed h h')
    · exact Or.inr (T.down_closed h h')⟩
  imp S T := ⟨{P | ∀ Q, (Q ⊢ P) → Q ∈ S.carrier → Q ∈ T.carrier}, by
    intro P R h hRP Q hQR hS
    exact h Q (hQR.trans hRP) hS⟩
  sForall Ψ := ⟨{P | ∀ S, Ψ S → P ∈ S.carrier}, by
    intro P Q h hQP S hS
    exact S.down_closed (h S hS) hQP⟩
  sExists Ψ := ⟨{P | ∃ S, Ψ S ∧ P ∈ S.carrier}, by
    intro P Q ⟨S, hS, hP⟩ hQP
    exact ⟨S, hS, S.down_closed hP hQP⟩⟩
  sep S T := down {R | ∃ P ∈ S.carrier, ∃ Q ∈ T.carrier, BIBase.sep P Q = R}
  wand S T := ⟨{R | ∀ P ∈ S.carrier, BIBase.sep R P ∈ T.carrier}, by
    intro R R' h hR'R P hP
    exact T.down_closed (h P hP) (sep_mono hR'R BIBase.Entails.rfl)⟩
  persistently S := down {R | ∃ P ∈ S.carrier, BIBase.persistently P = R}
  later S := down {R | ∃ P ∈ S.carrier, BIBase.later P = R}

@[simp] theorem mem_sep {S T : SIProp PROP} {R : PROP} :
    R ∈ (BIBase.sep S T).carrier ↔
      ∃ P ∈ S.carrier, ∃ Q ∈ T.carrier, R ⊢ BIBase.sep P Q := by
  change (∃ X, (∃ P ∈ S.carrier, ∃ Q ∈ T.carrier, BIBase.sep P Q = X) ∧ (R ⊢ X)) ↔ _
  constructor
  · rintro ⟨X, ⟨P, hP, Q, hQ, rfl⟩, hR⟩
    exact ⟨P, hP, Q, hQ, hR⟩
  · rintro ⟨P, hP, Q, hQ, hR⟩
    exact ⟨BIBase.sep P Q, ⟨P, hP, Q, hQ, rfl⟩, hR⟩

@[simp] theorem mem_persistently {S : SIProp PROP} {R : PROP} :
    R ∈ (BIBase.persistently S).carrier ↔
      ∃ P ∈ S.carrier, R ⊢ BIBase.persistently P := by
  change (∃ X, (∃ P ∈ S.carrier, BIBase.persistently P = X) ∧ (R ⊢ X)) ↔ _
  constructor
  · rintro ⟨X, ⟨P, hP, rfl⟩, hR⟩
    exact ⟨P, hP, hR⟩
  · rintro ⟨P, hP, hR⟩
    exact ⟨BIBase.persistently P, ⟨P, hP, rfl⟩, hR⟩

@[simp] theorem mem_later {S : SIProp PROP} {R : PROP} :
    R ∈ (BIBase.later S).carrier ↔
      ∃ P ∈ S.carrier, R ⊢ BIBase.later P := by
  change (∃ X, (∃ P ∈ S.carrier, BIBase.later P = X) ∧ (R ⊢ X)) ↔ _
  constructor
  · rintro ⟨X, ⟨P, hP, rfl⟩, hR⟩
    exact ⟨P, hP, hR⟩
  · rintro ⟨P, hP, hR⟩
    exact ⟨BIBase.later P, ⟨P, hP, rfl⟩, hR⟩

instance : BI (SIProp PROP) where
  entails_refl := fun h => h
  entails_trans h h' := fun _ hP => h' (h hP)
  equiv_iff := by
    intro P Q
    constructor
    · intro h
      cases h
      exact ⟨fun _ h => h, fun _ h => h⟩
    · intro h
      apply ext
      exact Set.Subset.antisymm h.1 h.2
  and_ne := ⟨fun _ _ _ h _ _ h' => by cases h; cases h'; rfl⟩
  or_ne := ⟨fun _ _ _ h _ _ h' => by cases h; cases h'; rfl⟩
  imp_ne := ⟨fun _ _ _ h _ _ h' => by cases h; cases h'; rfl⟩
  sForall_ne := by
    intro n Ψ₁ Ψ₂ h
    apply ext
    ext x
    constructor
    · intro hx S hS
      obtain ⟨T, hT, heq⟩ := h.2 S hS
      change T = S at heq
      subst S
      exact hx T hT
    · intro hx S hS
      obtain ⟨T, hT, heq⟩ := h.1 S hS
      change S = T at heq
      subst T
      exact hx S hT
  sExists_ne := by
    intro n Ψ₁ Ψ₂ h
    apply ext
    ext x
    constructor
    · rintro ⟨S, hS, hx⟩
      obtain ⟨T, hT, heq⟩ := h.1 S hS
      change S = T at heq
      subst T
      exact ⟨S, hT, hx⟩
    · rintro ⟨T, hT, hx⟩
      obtain ⟨S, hS, heq⟩ := h.2 T hT
      change S = T at heq
      subst T
      exact ⟨S, hS, hx⟩
  sep_ne := ⟨fun _ _ _ h _ _ h' => by cases h; cases h'; rfl⟩
  wand_ne := ⟨fun _ _ _ h _ _ h' => by cases h; cases h'; rfl⟩
  persistently_ne := ⟨fun _ _ _ h => by cases h; rfl⟩
  later_ne := ⟨fun _ _ _ h => by cases h; rfl⟩
  pure_intro := by
    intro φ P h R hR
    exact h
  pure_elim' := by
    intro φ P h R hR
    exact h hR trivial
  and_elim_l := fun h => h.1
  and_elim_r := fun h => h.2
  and_intro := fun h h' _ hP => ⟨h hP, h' hP⟩
  or_intro_l := fun h => Or.inl h
  or_intro_r := fun h => Or.inr h
  or_elim := by
    intro P Q R h h' x hx
    rcases hx with hx | hx
    · exact h hx
    · exact h' hx
  imp_intro := by
    intro P Q R h x hx y hyx hyQ
    exact h ⟨P.down_closed hx hyx, hyQ⟩
  imp_elim := by
    intro P Q R h x ⟨hxP, hxQ⟩
    exact (h hxP) x BIBase.Entails.rfl hxQ
  sForall_intro := by
    intro P Ψ h x hx Q hQ
    exact h Q hQ hx
  sForall_elim := by
    intro Ψ P h x hx
    exact hx P h
  sExists_intro := by
    intro Ψ P h x hx
    exact ⟨P, h, hx⟩
  sExists_elim := by
    intro Ψ Q h x ⟨P, hP, hx⟩
    exact h P hP hx
  sep_mono := by
    intro P P' Q Q' h h' x hx
    obtain ⟨p, hp, q, hq, hxpq⟩ := mem_sep.mp hx
    exact mem_sep.mpr ⟨p, h hp, q, h' hq, hxpq⟩
  emp_sep := by
    intro P
    constructor
    · intro x hx
      obtain ⟨e, he, p, hp, hxep⟩ := mem_sep.mp hx
      have he' : e ⊢ (BIBase.emp : PROP) := mem_down_singleton.mp he
      exact P.down_closed hp
        (hxep.trans ((sep_mono he' BIBase.Entails.rfl).trans emp_sep.mp))
    · intro x hx
      exact mem_sep.mpr ⟨BIBase.emp,
        mem_down_singleton.mpr BIBase.Entails.rfl, x, hx, emp_sep.mpr⟩
  sep_symm := by
    intro P Q x hx
    obtain ⟨p, hp, q, hq, hxpq⟩ := mem_sep.mp hx
    exact mem_sep.mpr ⟨q, hq, p, hp, hxpq.trans sep_symm⟩
  sep_assoc_l := by
    intro P Q R x hx
    obtain ⟨a, ha, r, hr, hxar⟩ := mem_sep.mp hx
    obtain ⟨p, hp, q, hq, hapq⟩ := mem_sep.mp ha
    have hqR : BIBase.sep q r ∈ (BIBase.sep Q R).carrier :=
      mem_sep.mpr ⟨q, hq, r, hr, BIBase.Entails.rfl⟩
    refine mem_sep.mpr ⟨p, hp, BIBase.sep q r, hqR, ?_⟩
    exact hxar.trans ((sep_mono hapq BIBase.Entails.rfl).trans sep_assoc_l)
  wand_intro := by
    intro P Q R h x hx q hq
    exact h (mem_sep.mpr ⟨x, hx, q, hq, BIBase.Entails.rfl⟩)
  wand_elim := by
    intro P Q R h x hx
    obtain ⟨p, hp, q, hq, hxpq⟩ := mem_sep.mp hx
    exact R.down_closed ((h hp) q hq) hxpq
  persistently_mono := by
    intro P Q h x hx
    obtain ⟨p, hp, hxp⟩ := mem_persistently.mp hx
    exact mem_persistently.mpr ⟨p, h hp, hxp⟩
  persistently_idem_2 := by
    intro P x hx
    obtain ⟨p, hp, hxp⟩ := mem_persistently.mp hx
    have hp' : BIBase.persistently p ∈ (BIBase.persistently P).carrier :=
      mem_persistently.mpr ⟨p, hp, BIBase.Entails.rfl⟩
    exact mem_persistently.mpr
      ⟨BIBase.persistently p, hp', hxp.trans persistently_idem_2⟩
  persistently_emp_2 := by
    intro x hx
    have hxemp : x ⊢ (BIBase.emp : PROP) := mem_down_singleton.mp hx
    have hemp : (BIBase.emp : PROP) ∈ (BIBase.emp : SIProp PROP).carrier :=
      mem_down_singleton.mpr BIBase.Entails.rfl
    exact mem_persistently.mpr ⟨BIBase.emp, hemp, hxemp.trans persistently_emp_2⟩
  persistently_and_2 := by
    intro P Q x hx
    obtain ⟨p, hp, hxp⟩ := mem_persistently.mp hx.1
    obtain ⟨q, hq, hxq⟩ := mem_persistently.mp hx.2
    have hpq : BIBase.and p q ∈ (BIBase.and P Q).carrier :=
      ⟨P.down_closed hp and_elim_l, Q.down_closed hq and_elim_r⟩
    have hboth : x ⊢ BIBase.and (BIBase.persistently p) (BIBase.persistently q) :=
      and_intro hxp hxq
    exact mem_persistently.mpr
      ⟨BIBase.and p q, hpq, hboth.trans persistently_and_2⟩
  persistently_absorb_l := by
    intro P Q x hx
    obtain ⟨a, ha, q, hq, hxa⟩ := mem_sep.mp hx
    obtain ⟨p, hp, hap⟩ := mem_persistently.mp ha
    exact mem_persistently.mpr
      ⟨p, hp, hxa.trans ((sep_mono hap BIBase.Entails.rfl).trans persistently_absorb_l)⟩
  persistently_and_l := by
    intro P Q x hx
    obtain ⟨p, hp, hxp⟩ := mem_persistently.mp hx.1
    have hxx : x ⊢ BIBase.and (BIBase.persistently p) x :=
      and_intro hxp BIBase.Entails.rfl
    exact mem_sep.mpr ⟨p, hp, x, hx.2, hxx.trans persistently_and_l⟩
  later_mono := by
    intro P Q h x hx
    obtain ⟨p, hp, hxp⟩ := mem_later.mp hx
    exact mem_later.mpr ⟨p, h hp, hxp⟩
  later_intro := by
    intro P x hx
    exact mem_later.mpr ⟨x, hx, later_intro⟩
  later_sForall_2 := by
    intro Φ x hx
    let A : Set (PROP) :=
      {q | (x ⊢ BIBase.later q) ∧ ∃ S : SIProp PROP, Φ S ∧ q ∈ S.carrier}
    let m : PROP := BIBase.sForall A
    have hxm : x ⊢ BIBase.later m := by
      have hleft : x ⊢ (∀ q : PROP, BIBase.imp (BIBase.pure (A q)) (BIBase.later q)) := by
        apply forall_intro
        intro q
        apply BI.imp_intro
        apply pure_elim_right
        intro hA
        exact hA.1
      exact hleft.trans (later_sForall_2 (PROP := PROP) (Φ := A))
    have hm : m ∈ (BIBase.sForall Φ).carrier := by
      intro S hS
      have hximp : x ∈ (BIBase.imp (BIBase.pure (Φ S)) (BIBase.later S)).carrier :=
        hx _ ⟨S, rfl⟩
      have hxS : x ∈ (BIBase.later S).carrier :=
        hximp x BIBase.Entails.rfl hS
      obtain ⟨q, hq, hxq⟩ := mem_later.mp hxS
      have hqA : q ∈ A := ⟨hxq, S, hS, hq⟩
      exact S.down_closed hq (sForall_elim hqA)
    exact mem_later.mpr ⟨m, hm, hxm⟩
  later_sExists_false := by
    intro Φ x hx
    obtain ⟨a, ⟨P, hP, ha⟩, hxa⟩ := mem_later.mp hx
    right
    refine ⟨BIBase.and (BIBase.pure (Φ P)) (BIBase.later P), ?_, ?_⟩
    · exact ⟨P, rfl⟩
    · exact ⟨hP, mem_later.mpr ⟨a, ha, hxa⟩⟩
  later_sep := by
    intro P Q
    constructor
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := mem_later.mp hx
      obtain ⟨p, hp, q, hq, hapq⟩ := mem_sep.mp ha
      have hp' : BIBase.later p ∈ (BIBase.later P).carrier :=
        mem_later.mpr ⟨p, hp, BIBase.Entails.rfl⟩
      have hq' : BIBase.later q ∈ (BIBase.later Q).carrier :=
        mem_later.mpr ⟨q, hq, BIBase.Entails.rfl⟩
      exact mem_sep.mpr ⟨BIBase.later p, hp', BIBase.later q, hq',
        hxa.trans ((later_mono hapq).trans later_sep.mp)⟩
    · intro x hx
      obtain ⟨a, ha, b, hb, hxab⟩ := mem_sep.mp hx
      obtain ⟨p, hp, hap⟩ := mem_later.mp ha
      obtain ⟨q, hq, hbq⟩ := mem_later.mp hb
      have hpq : BIBase.sep p q ∈ (BIBase.sep P Q).carrier :=
        mem_sep.mpr ⟨p, hp, q, hq, BIBase.Entails.rfl⟩
      exact mem_later.mpr ⟨BIBase.sep p q, hpq,
        hxab.trans ((sep_mono hap hbq).trans later_sep.mpr)⟩
  later_persistently := by
    intro P
    constructor
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := mem_later.mp hx
      obtain ⟨p, hp, hap⟩ := mem_persistently.mp ha
      have hp' : BIBase.later p ∈ (BIBase.later P).carrier :=
        mem_later.mpr ⟨p, hp, BIBase.Entails.rfl⟩
      exact mem_persistently.mpr ⟨BIBase.later p, hp',
        hxa.trans ((later_mono hap).trans later_persistently.mp)⟩
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := mem_persistently.mp hx
      obtain ⟨p, hp, hap⟩ := mem_later.mp ha
      have hp' : BIBase.persistently p ∈ (BIBase.persistently P).carrier :=
        mem_persistently.mpr ⟨p, hp, BIBase.Entails.rfl⟩
      exact mem_later.mpr ⟨BIBase.persistently p, hp',
        hxa.trans ((persistently_mono hap).trans later_persistently.mpr)⟩
  later_false_em := by
    intro P x hx
    right
    intro y hyx hyFalse
    obtain ⟨p, hp, _⟩ := mem_later.mp hyFalse
    exact False.elim hp

/-- SIProp entailment is exactly the requested Hoare condition. -/
theorem entails_iff_hoare (S T : SIProp PROP) :
    (S ⊢ T) ↔ ∀ P ∈ S.carrier, ∃ Q ∈ T.carrier, P ⊢ Q :=
  (hoareEntails_iff_subset S T).symm

/-- Principal propositions retain the underlying entailment. -/
theorem lift_bi_entails_iff (P Q : PROP) :
    (lift P ⊢ lift Q) ↔ (P ⊢ Q) :=
  (entails_iff_hoare (lift P) (lift Q)).trans (lift_entails_iff P Q)

/-- Two choices entail a singleton exactly when each choice entails it. -/
theorem down_pair_bi_entails_iff (P₁ P₂ Q : PROP) :
    (down {P₁, P₂} ⊢ down {Q}) ↔ (P₁ ⊢ Q) ∧ (P₂ ⊢ Q) :=
  (entails_iff_hoare (down {P₁, P₂}) (down {Q})).trans
    (down_pair_entails_iff P₁ P₂ Q)

/-- The principal embedding preserves separating conjunction. -/
theorem lift_sep (P Q : PROP) :
    BIBase.sep (lift P) (lift Q) = lift (BIBase.sep P Q) := by
  apply ext
  ext R
  constructor
  · intro hR
    obtain ⟨p, hp, q, hq, hRpq⟩ := mem_sep.mp hR
    exact mem_down_singleton.mpr
      (hRpq.trans (sep_mono (mem_down_singleton.mp hp) (mem_down_singleton.mp hq)))
  · intro hR
    exact mem_sep.mpr ⟨P, mem_down_singleton.mpr BIBase.Entails.rfl,
      Q, mem_down_singleton.mpr BIBase.Entails.rfl, mem_down_singleton.mp hR⟩

theorem nondeterministic_skolemization {Ps : Set (PROP)} {Q : PROP} (hPs : ∃ p ∈ Ps, ⊢ p) (hQ : down Ps ⊢ lift Q) :
    ⊢ Q := by
  obtain ⟨p, hp, hP⟩ := hPs
  rw [entails_iff_hoare] at hQ
  specialize hQ p
  simp at hQ
  specialize hQ p hp BI.entails_refl
  let ⟨Q', hQ', hPQ'⟩ := hQ
  have := hPQ'.trans hQ'
  exact hP.trans this

theorem peirce (A B : Prop) (em : ∀ p : Prop, p ∨ ¬p) : ((A -> B) -> A) -> A := by
  specialize em A
  apply Or.elim em
  · exact fun a _ => a
  · intro cn
    have : A -> B := (fun a => False.elim (cn a))
    intro h
    exact h this

end SIProp
end Skolemization
