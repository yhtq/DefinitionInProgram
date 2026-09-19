import ITree.EffectAlgebra

/-!
# Translating interaction-tree effects

This module ports the part of the Interaction Trees `TranslateFacts` API used
throughout the Program Logics à la Carte development.
-/

namespace ITree

universe u u₁ u₂ u₃ uₒ

variable {ε₁ : Type u → Type u₁} {ε₂ : Type u → Type u₂}
  {ε₃ : Type u → Type u₃} {ρ : Type uₒ}

/-- Rename every visible event of an interaction tree along a natural
transformation. Silent steps and return values are preserved. -/
def translate (f : ε₁ ⟶ ε₂) (t : ITree ε₁ ρ) : ITree ε₂ ρ :=
  .corecEmbed (fun t =>
    match t.dest with
    | ⟨.ret x, _⟩ => .inl (ret x)
    | ⟨.tau, c⟩ => .inr (tau' (.inr (c 0)))
    | ⟨.vis α e, k⟩ => .inr (vis' (@f α e) (fun x => .inr (k x)))) t

@[simp]
theorem translate_ret (f : ε₁ ⟶ ε₂) (x : ρ) :
    translate f (@ret ε₁ ρ x) = @ret ε₂ ρ x := by
  conv => lhs; simp only [translate]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem translate_tau (f : ε₁ ⟶ ε₂) (t : ITree ε₁ ρ) :
    translate f (tau t) = tau (translate f t) := by
  conv => lhs; simp only [translate]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem translate_vis (f : ε₁ ⟶ ε₂) {α : Type u}
    (e : ε₁ α) (k : α → ITree ε₁ ρ) :
    translate f (@vis ε₁ ρ α e k) =
      @vis ε₂ ρ α (@f α e) (fun x => translate f (k x)) := by
  conv => lhs; simp only [translate]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem translate_id (t : ITree ε₁ ρ) :
    translate (fun e => e) t = t := by
  apply eq_of_bisim_state
      (lhs := fun t => translate (fun e => e) t)
      (rhs := fun t => t)
  · intro s
    apply s.dMatchOn
    · intro x hx
      rw [hx, translate_ret]
      exact .ret x
    · intro t ht
      rw [ht, translate_tau]
      exact .tau _ _ (Or.inr ⟨t, rfl, rfl⟩)
    · intro α e k hk
      rw [hk, translate_vis]
      exact .vis e _ _ (fun x => Or.inr ⟨k x, rfl, rfl⟩)

@[simp]
theorem translate_comp (g : ε₂ ⟶ ε₃) (f : ε₁ ⟶ ε₂)
    (t : ITree ε₁ ρ) :
    translate g (translate f t) = translate (fun e => g (f e)) t := by
  apply eq_of_bisim_state
      (lhs := fun t => translate g (translate f t))
      (rhs := fun t => translate (fun e => g (f e)) t)
  · intro s
    apply s.dMatchOn
    · intro x hx
      rw [hx, translate_ret, translate_ret, translate_ret]
      exact .ret x
    · intro t ht
      rw [ht, translate_tau, translate_tau, translate_tau]
      exact .tau _ _ (Or.inr ⟨t, rfl, rfl⟩)
    · intro α e k hk
      rw [hk, translate_vis, translate_vis, translate_vis]
      exact .vis (g (f e)) _ _ (fun x => Or.inr ⟨k x, rfl, rfl⟩)

end ITree
