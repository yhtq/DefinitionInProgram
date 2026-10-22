import IrisUtil.Fractional
import Iris.Instances.Lib.FUpd
import Iris.Instances.Lib.Invariants

open Iris Iris.BI

example {GF : BundledGFunctors} {A : Type} [GhostVarG GF A]
    (γ : GName) (a₁ a₂ : A) (q₁ q₂ : Qp) :
    (iprop(ghost_var (GF := GF) γ (.own q₁) a₁ ∗
      ghost_var γ (.own q₂) a₂) : IProp GF) ⊢
      iprop(⌜a₁ = a₂⌝ ∧
        (ghost_var γ (.own q₁) a₁ ∗ ghost_var γ (.own q₂) a₂)) := by
  iintro ⟨Hleft, Hright⟩
  frac_agree Hleft Hright as %heq
  isplit
  · ipureintro
    exact heq
  · iframe

example {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    {A : Type} [GhostVarG GF A]
    (γ : GName) (a b : A) (q₁ q₂ : Qp) (hfull : q₁ + q₂ = 1) :
    (iprop(ghost_var (GF := GF) γ (.own q₁) a ∗ ghost_var γ (.own q₂) a) : IProp GF) ⊢
      iprop(|={∅}=> ghost_var γ (.own q₁) b ∗ ghost_var γ (.own q₂) b) := by
  iintro ⟨Hleft, Hright⟩
  frac_agree Hleft Hright as %heq
  frac_update Hleft Hright to b with ⟨Hleft', Hright'⟩
  · exact hfull
  imodintro
  iframe

example {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    {A : Type} [GhostVarG GF A]
    (γ : GName) (a b : A) (q₁ q₂ : Qp) (hfull : q₁ + q₂ = 1) :
    (iprop(ghost_var (GF := GF) γ (.own q₁) a ∗ ghost_var γ (.own q₂) a) : IProp GF) ⊢
      iprop(|={∅}=> ghost_var γ (.own q₁) b ∗ ghost_var γ (.own q₂) b) := by
  iintro ⟨Hleft, Hright⟩
  frac_agree Hleft Hright using Iris.ghost_var_agree as %heq
  frac_update Hleft Hright to b using Iris.ghost_var_update_2 with ⟨Hleft', Hright'⟩
  · exact hfull
  imodintro
  iframe

example {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    {A : Type} [GhostVarG GF A]
    (γ : GName) (a b : A) (q₁ q₂ : Qp) (hfull : q₁ + q₂ = 1) :
    (iprop(ghost_var (GF := GF) γ (.own q₁) a ∗ ghost_var γ (.own q₂) a) : IProp GF) ⊢
      iprop(|={∅}=> ghost_var γ (.own q₁) b ∗ ghost_var γ (.own q₂) b) := by
  iintro ⟨H₁, H₂⟩
  frac_update [H₁ : q₁, H₂ : q₂] to b with [X, Y]
  · exact hfull
  imodintro
  isplitl [X]
  · iexact X
  · iexact Y

-- The ownerships may initially describe different values: agreement and the
-- update still work without discarding any of their fractions.
example {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    {A : Type} [GhostVarG GF A]
    (γ : GName) (a₀ a₁ a₂ b : A) (q₀ q₁ q₂ : Qp)
    (hfull : q₀ + q₁ + q₂ = 1) :
    (iprop(ghost_var (GF := GF) γ (.own q₀) a₀ ∗
      ghost_var γ (.own q₁) a₁ ∗ ghost_var γ (.own q₂) a₂) : IProp GF) ⊢
      iprop(|={∅}=> ghost_var γ (.own q₀) b ∗
        ghost_var γ (.own q₁) b ∗ ghost_var γ (.own q₂) b) := by
  iintro ⟨H₀, H₁, H₂⟩
  frac_agree [H₀, H₁, H₂] as [eq₁, eq₂]
  frac_update [H₀, H₁, H₂] to b with [H₀', H₁', H₂']
  · exact hfull
  imodintro
  iframe
