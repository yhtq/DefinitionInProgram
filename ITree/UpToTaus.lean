import ITree.Monad

/-!
# Interaction-tree equivalence up to silent steps

`IEquttF sim` compares one observable layer of two interaction trees. A
matching pair of `tau`s is discharged through `sim`, while `tauLeft` and
`tauRight` permit a finite number of unmatched silent steps before that
observable layer. Taking the greatest fixed point gives `IEqutt`.

This is the `b1 = b2 = true` specialization of Interaction Trees' `eqitF`.
In particular, the recursive premises of `tauLeft` and `tauRight` are
inductive: one observation may ignore only finitely many silent steps.
-/

namespace ITree

universe u₁ u₂ u₃ v

variable {ε : Type u₁ → Type v} {ρ : Type u₂}

/-- One observable layer of weak bisimulation. The recursive occurrences in
`tauLeft` and `tauRight` account for a finite run of unmatched silent steps. -/
@[grind]
inductive IEquttF (sim : ITree ε ρ → ITree ε ρ → Prop) :
    ITree ε ρ → ITree ε ρ → Prop where
  | ret (x : ρ) : IEquttF sim (ret x) (ret x)
  | tau (t₁ t₂ : ITree ε ρ) (h : sim t₁ t₂) :
      IEquttF sim (tau t₁) (tau t₂)
  | vis {α : Type u₁} (e : ε α) (k₁ k₂ : α → ITree ε ρ)
      (h : ∀ x, sim (k₁ x) (k₂ x)) :
      IEquttF sim (vis e k₁) (vis e k₂)
  | tauLeft (t₁ t₂ : ITree ε ρ) (h : IEquttF sim t₁ t₂) :
      IEquttF sim (tau t₁) t₂
  | tauRight (t₁ t₂ : ITree ε ρ) (h : IEquttF sim t₁ t₂) :
      IEquttF sim t₁ (tau t₂)

/-- `IEquttF` is monotone in its coinductive hypothesis. -/
theorem IEquttF_monotone
    {sim sim' : ITree ε ρ → ITree ε ρ → Prop}
    (hmono : ∀ t₁ t₂, sim t₁ t₂ → sim' t₁ t₂) :
    ∀ {t₁ t₂}, IEquttF sim t₁ t₂ → IEquttF sim' t₁ t₂ := by
  intro t₁ t₂ h
  induction h with
  | ret x => exact .ret x
  | tau t₁ t₂ h => exact .tau t₁ t₂ (hmono t₁ t₂ h)
  | vis e k₁ k₂ h => exact .vis e k₁ k₂ (fun x => hmono _ _ (h x))
  | tauLeft t₁ t₂ _ ih => exact .tauLeft t₁ t₂ ih
  | tauRight t₁ t₂ _ ih => exact .tauRight t₁ t₂ ih

/-- The weak-bisimulation operator, put in reverse implication order so its
least fixed point is the greatest predicate fixed point. -/
def IEquttOp
    (sim : ITree ε ρ → ITree ε ρ → Lean.Order.ReverseImplicationOrder) :
    ITree ε ρ → ITree ε ρ → Lean.Order.ReverseImplicationOrder :=
  fun t₁ t₂ => IEquttF sim t₁ t₂

theorem IEquttOp_monotone : Lean.Order.monotone (@IEquttOp ε ρ) := by
  intro sim sim' hsim t₁ t₂ h
  exact IEquttF_monotone (fun a b => hsim a b) h

/-- Weak bisimulation: interaction-tree equivalence up to finite runs of
silent (`tau`) steps. -/
noncomputable def IEqutt (t₁ t₂ : ITree ε ρ) : Prop :=
  reverseToProp
    (Lean.Order.lfp_monotone (@IEquttOp ε ρ) IEquttOp_monotone t₁ t₂)

abbrev Eutt := @IEqutt

infix:50 " ≈τ " => IEqutt

/-- Unfold one observable layer of weak bisimulation. -/
theorem IEqutt_unfold (t₁ t₂ : ITree ε ρ) :
    IEqutt t₁ t₂ ↔ IEquttF IEqutt t₁ t₂ := by
  unfold IEqutt reverseToProp
  delta Lean.Order.lfp_monotone
  conv_lhs => rw [Lean.Order.lfp_fix IEquttOp_monotone]
  rfl

/-- Coinduction principle for weak bisimulation. -/
theorem IEqutt_coinduct (R : ITree ε ρ → ITree ε ρ → Prop)
    (hstep : ∀ t₁ t₂, R t₁ t₂ → IEquttF R t₁ t₂) :
    ∀ t₁ t₂, R t₁ t₂ → IEqutt t₁ t₂ := by
  have hpost : Lean.Order.PartialOrder.rel
      (@IEquttOp ε ρ
        (fun t₁ t₂ => (R t₁ t₂ : Lean.Order.ReverseImplicationOrder)))
      (fun t₁ t₂ => (R t₁ t₂ : Lean.Order.ReverseImplicationOrder)) := by
    change ∀ t₁ t₂, R t₁ t₂ → IEquttF R t₁ t₂
    exact hstep
  have hlfp := Lean.Order.lfp_le_of_le hpost
  intro t₁ t₂ hR
  unfold IEqutt reverseToProp
  exact hlfp t₁ t₂ hR

theorem iequtt_ret (x : ρ) : IEqutt (ret x : ITree ε ρ) (ret x) := by
  rw [IEqutt_unfold]
  exact .ret x

theorem iequtt_tau {t₁ t₂ : ITree ε ρ} (h : IEqutt t₁ t₂) :
    IEqutt (tau t₁) (tau t₂) := by
  rw [IEqutt_unfold]
  exact .tau t₁ t₂ h

theorem iequtt_vis {α : Type u₁} (e : ε α) (k₁ k₂ : α → ITree ε ρ)
    (h : ∀ x, IEqutt (k₁ x) (k₂ x)) :
    IEqutt (vis e k₁) (vis e k₂) := by
  rw [IEqutt_unfold]
  exact .vis e k₁ k₂ h

theorem iequtt_tau_left {t₁ t₂ : ITree ε ρ} (h : IEqutt t₁ t₂) :
    IEqutt (tau t₁) t₂ := by
  rw [IEqutt_unfold] at h ⊢
  exact .tauLeft t₁ t₂ h

theorem iequtt_tau_right {t₁ t₂ : ITree ε ρ} (h : IEqutt t₁ t₂) :
    IEqutt t₁ (tau t₂) := by
  rw [IEqutt_unfold] at h ⊢
  exact .tauRight t₁ t₂ h

theorem iequtt_tauN_left (n : Nat) {t₁ t₂ : ITree ε ρ}
    (h : IEqutt t₁ t₂) : IEqutt (tauN n t₁) t₂ := by
  induction n with
  | zero => exact h
  | succ n ih => exact iequtt_tau_left ih

theorem iequtt_tauN_right (n : Nat) {t₁ t₂ : ITree ε ρ}
    (h : IEqutt t₁ t₂) : IEqutt t₁ (tauN n t₂) := by
  induction n with
  | zero => exact h
  | succ n ih => exact iequtt_tau_right ih

/-- Flipping one weak-bisimulation layer flips its simulation hypothesis. -/
theorem IEquttF_flip
    {sim : ITree ε ρ → ITree ε ρ → Prop}
    {t₁ t₂ : ITree ε ρ} (h : IEquttF sim t₁ t₂) :
    IEquttF (fun a b => sim b a) t₂ t₁ := by
  induction h with
  | ret x => exact .ret x
  | tau t₁ t₂ h => exact .tau t₂ t₁ h
  | vis e k₁ k₂ h => exact .vis e k₂ k₁ h
  | tauLeft t₁ t₂ _ ih => exact .tauRight t₂ t₁ ih
  | tauRight t₁ t₂ _ ih => exact .tauLeft t₂ t₁ ih

/-- Weak bisimulation is reflexive. -/
@[refl]
theorem iequtt_refl (t : ITree ε ρ) : IEqutt t t := by
  apply IEqutt_coinduct Eq
  · intro t₁ t₂ h
    subst t₂
    apply t₁.dMatchOn
    · intro x hx
      rw [hx]
      exact .ret x
    · intro t ht
      rw [ht]
      exact .tau t t rfl
    · intro α e k hk
      rw [hk]
      exact .vis e k k (fun _ => rfl)
  · exact rfl

/-- Weak bisimulation is symmetric. -/
@[symm]
theorem iequtt_symm {t₁ t₂ : ITree ε ρ} (h : IEqutt t₁ t₂) :
    IEqutt t₂ t₁ := by
  apply IEqutt_coinduct (fun a b => IEqutt b a)
  · intro a b hab
    rw [IEqutt_unfold] at hab
    exact IEquttF_flip hab
  · exact h

/-- Definitional equality is contained in weak bisimulation. -/
theorem iequtt_of_eq {t₁ t₂ : ITree ε ρ} (h : t₁ = t₂) : IEqutt t₁ t₂ := by
  subst t₂
  exact iequtt_refl t₁

/-- Strong interaction-tree equality is contained in weak bisimulation. -/
theorem iequtt_of_ieq {t₁ t₂ : ITree ε ρ} (h : IEq t₁ t₂) : IEqutt t₁ t₂ :=
  iequtt_of_eq ((ieq_iff_eq t₁ t₂).mp h)

theorem iequtt_tauN (m n : Nat) (t : ITree ε ρ) :
    IEqutt (tauN m t) (tauN n t) :=
  iequtt_tauN_right n (iequtt_tauN_left m (iequtt_refl t))

/-- Remove one known leading `tau` from the left index of an unfolded
weak-bisimulation proof. The extra disjunct is the coinductive hypothesis used
by `iequtt_tau_left_inv`. -/
private theorem IEquttF_remove_tau_left {t₁ t₂ : ITree ε ρ}
    (h : IEquttF IEqutt (tau t₁) t₂) :
    IEquttF (fun a b => IEqutt a b ∨ IEqutt (tau a) b) t₁ t₂ := by
  generalize hleft : tau t₁ = left at h
  induction h generalizing t₁ with
  | ret x =>
      itree_elim hleft
  | tau a b hab =>
      have ha : t₁ = a := tau_inj hleft
      subst a
      apply IEquttF.tauRight
      apply IEquttF_monotone (sim := IEqutt) (fun x y hxy => Or.inl hxy)
      exact (IEqutt_unfold t₁ b).mp hab
  | vis e k₁ k₂ hk =>
      itree_elim hleft
  | tauLeft a b hab ih =>
      have ha : t₁ = a := tau_inj hleft
      subst a
      exact IEquttF_monotone (sim := IEqutt) (fun x y hxy => Or.inl hxy) hab
  | tauRight a b hab ih =>
      exact .tauRight t₁ b (ih hleft)

/-- A leading silent step may be removed on the left. -/
theorem iequtt_tau_left_inv {t₁ t₂ : ITree ε ρ}
    (h : IEqutt (tau t₁) t₂) : IEqutt t₁ t₂ := by
  apply IEqutt_coinduct (fun a b => IEqutt a b ∨ IEqutt (tau a) b)
  · intro a b hab
    rcases hab with hab | hab
    · exact IEquttF_monotone (sim := IEqutt) (fun x y hxy => Or.inl hxy)
        ((IEqutt_unfold a b).mp hab)
    · exact IEquttF_remove_tau_left ((IEqutt_unfold (tau a) b).mp hab)
  · exact Or.inr h

/-- A leading silent step may be removed on the right. -/
theorem iequtt_tau_right_inv {t₁ t₂ : ITree ε ρ}
    (h : IEqutt t₁ (tau t₂)) : IEqutt t₁ t₂ :=
  iequtt_symm (iequtt_tau_left_inv (iequtt_symm h))

@[simp]
theorem iequtt_tau_left_iff (t₁ t₂ : ITree ε ρ) :
    IEqutt (tau t₁) t₂ ↔ IEqutt t₁ t₂ :=
  ⟨iequtt_tau_left_inv, iequtt_tau_left⟩

@[simp]
theorem iequtt_tau_right_iff (t₁ t₂ : ITree ε ρ) :
    IEqutt t₁ (tau t₂) ↔ IEqutt t₁ t₂ :=
  ⟨iequtt_tau_right_inv, iequtt_tau_right⟩

@[simp]
theorem iequtt_tauN_left_iff (n : Nat) (t₁ t₂ : ITree ε ρ) :
    IEqutt (tauN n t₁) t₂ ↔ IEqutt t₁ t₂ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tauN, iequtt_tau_left_iff, ih]

@[simp]
theorem iequtt_tauN_right_iff (n : Nat) (t₁ t₂ : ITree ε ρ) :
    IEqutt t₁ (tauN n t₂) ↔ IEqutt t₁ t₂ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tauN, iequtt_tau_right_iff, ih]

section Bind

variable {α : Type u₃}

private def BindClosure (k₁ k₂ : α → ITree ε ρ)
    (a b : ITree ε ρ) : Prop :=
  IEqutt a b ∨
    ∃ t₁ t₂ : ITree ε α,
      IEqutt t₁ t₂ ∧ a = bind t₁ k₁ ∧ b = bind t₂ k₂

private theorem IEquttF_bind
    (k₁ k₂ : α → ITree ε ρ)
    (hk : ∀ x, IEqutt (k₁ x) (k₂ x))
    {t₁ t₂ : ITree ε α} (h : IEquttF IEqutt t₁ t₂) :
    IEquttF (BindClosure k₁ k₂) (bind t₁ k₁) (bind t₂ k₂) := by
  induction h with
  | ret x =>
      rw [bind_ret, bind_ret]
      apply IEquttF_monotone (sim := IEqutt)
          (fun a b hab => (Or.inl hab : BindClosure k₁ k₂ a b))
      exact (IEqutt_unfold (k₁ x) (k₂ x)).mp (hk x)
  | tau t₁ t₂ h =>
      rw [bind_tau, bind_tau]
      exact .tau _ _ (Or.inr ⟨t₁, t₂, h, rfl, rfl⟩)
  | vis e c₁ c₂ h =>
      rw [bind_vis, bind_vis]
      exact .vis e _ _ (fun x => Or.inr ⟨c₁ x, c₂ x, h x, rfl, rfl⟩)
  | tauLeft t₁ t₂ _ ih =>
      rw [bind_tau]
      exact .tauLeft _ _ ih
  | tauRight t₁ t₂ _ ih =>
      rw [bind_tau]
      exact .tauRight _ _ ih

/-- `bind` respects weak bisimulation in both the tree and continuation. -/
theorem iequtt_bind (k₁ k₂ : α → ITree ε ρ)
    {t₁ t₂ : ITree ε α} (ht : IEqutt t₁ t₂)
    (hk : ∀ x, IEqutt (k₁ x) (k₂ x)) :
    IEqutt (bind t₁ k₁) (bind t₂ k₂) := by
  apply IEqutt_coinduct (BindClosure k₁ k₂)
  · intro a b hab
    rcases hab with hab | ⟨s₁, s₂, hs, rfl, rfl⟩
    · apply IEquttF_monotone (sim := IEqutt)
          (fun x y hxy => (Or.inl hxy : BindClosure k₁ k₂ x y))
      exact (IEqutt_unfold a b).mp hab
    · exact IEquttF_bind k₁ k₂ hk ((IEqutt_unfold s₁ s₂).mp hs)
  · exact Or.inr ⟨t₁, t₂, ht, rfl, rfl⟩

theorem iequtt_bind_left (k : α → ITree ε ρ)
    {t₁ t₂ : ITree ε α} (h : IEqutt t₁ t₂) :
    IEqutt (bind t₁ k) (bind t₂ k) :=
  iequtt_bind k k h (fun x => iequtt_refl (k x))

/-- Inserting one silent step at every return point does not change a bind. -/
theorem bind_tau_right (t : ITree ε α) (k : α → ITree ε ρ) :
    IEqutt (bind t (fun x => tau (k x))) (bind t k) :=
  iequtt_bind (fun x => tau (k x)) k (iequtt_refl t)
    (fun x => iequtt_tau_left (iequtt_refl (k x)))

theorem iequtt_map (f : α → ρ) {t₁ t₂ : ITree ε α}
    (h : IEqutt t₁ t₂) : IEqutt (map f t₁) (map f t₂) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact iequtt_bind_left (pure ∘ f) h

end Bind

end ITree
