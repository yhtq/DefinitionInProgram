import ProgramLogicCarte.Wpi

/-! Structural rules for interaction-tree weakest preconditions. -/
namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE ITree

universe u v uρ

private def wpiWandPred {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandler GF ε)
    (state : WpiState GF ε ρ) : IProp GF :=
  iprop(∀ Ψ : ρ → IProp GF,
    (∀ r : ρ, (|={∅}=> state.2 r) -∗ (|={∅}=> Ψ r)) -∗
      wpi H state.1.car Ψ)

private instance wpiWandPred_ne {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandler GF ε) :
    NonExpansive (wpiWandPred (ρ := ρ) H) where
  ne := by
    intro n state₁ state₂ hstate
    rcases state₁ with ⟨⟨t₁⟩, Φ₁⟩
    rcases state₂ with ⟨⟨t₂⟩, Φ₂⟩
    rcases hstate with ⟨ht, hΦ⟩
    obtain rfl := DiscreteO.dist_inj ht
    unfold wpiWandPred
    exact forall_ne fun Ψ =>
      wand_ne.ne (forall_ne fun r =>
        wand_ne.ne (fupd_ne.ne (hΦ r)) .rfl) .rfl

private theorem fin1Const_zero {α : Type*} (value : α) :
    fin1Const value 0 = value := by
  rfl

/-- General postcondition strengthening at the empty execution mask. -/
theorem wpi_upd_wand {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandler GF ε)
    (t : ITree ε ρ) (Φ Ψ : ρ → IProp GF) :
    ⊢ iprop((∀ r, (|={∅}=> Φ r) -∗ (|={∅}=> Ψ r)) -∗
      wpi H t Φ -∗ wpi H t Ψ) := by
  iintro Hwand Hwp
  ihave Hgen : iprop(∀ state : WpiState GF ε ρ,
      wpi H state.1.car state.2 -∗ wpiWandPred H state) $$ []
  · iapply (wpi_iter H (wpiWandPred (ρ := ρ) H))
    iintro !> %state HF
    rcases state with ⟨⟨tree⟩, post⟩
    apply tree.dMatchOn
    · intro value htree
      subst tree
      isimp only [wpiF', wpiF, dest_ret] at HF
      isimp only [wpiWandPred]
      iintro %post' Hwand'
      rw [wpi_ret]
      ispecialize Hwand' $$ %value
      iapply Hwand' $$ HF
    · intro child htree
      subst tree
      isimp only [wpiF', wpiF, dest_tau] at HF
      isimp only [wpiWandPred]
      iintro %post' Hwand'
      rw [wpi_tau_step]
      imod HF with HF
      imodintro
      isimp only [wpiWandPred] at HF
      ispecialize HF $$ %post'
      isimp only [fin1Const_zero] at HF
      iapply HF
      iexact Hwand'
    · intro α event continuation htree
      subst tree
      isimp only [wpiF', wpiF, dest_vis] at HF
      isimp only [wpiWandPred]
      iintro %post' Hwand'
      rw [wpi_vis]
      imod HF with HF
      imodintro
      iapply (H.mono event
        (fun a => wpiWandPred H (⟨⟨continuation a⟩, post⟩))
        (fun a => wpi H (continuation a) post')
        (fun a => fupd ⊤ ∅ (wpiWandPred H
          (⟨⟨continuation a⟩, fun _ => iprop(False)⟩)))
        (fun a => fupd ⊤ ∅ (wpi H (continuation a) (fun _ => iprop(False))))) $$ [Hwand'] [] HF
      · iintro %a Ha
        isimp only [wpiWandPred] at Ha
        ispecialize Ha $$ %post'
        iapply Ha
        iexact Hwand'
      · iintro !> %a Ha
        imod Ha with Ha
        imodintro
        isimp only [wpiWandPred] at Ha
        ispecialize Ha $$ %(fun _ => iprop(False))
        iapply Ha
        iintro %r Hfalse
        iexact Hfalse
  ispecialize Hgen $$ %(⟨⟨t⟩, Φ⟩)
  ispecialize Hgen $$ Hwp
  isimp only [wpiWandPred] at Hgen
  ispecialize Hgen $$ %Ψ
  iapply Hgen $$ Hwand

/-- The usual WPi consequence rule. -/
theorem wpi_wand {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandler GF ε)
    (t : ITree ε ρ) (Φ Ψ : ρ → IProp GF) :
    ⊢ iprop((∀ r, Φ r -∗ Ψ r) -∗ wpi H t Φ -∗ wpi H t Ψ) := by
  iintro Hwand Hwp
  iapply (wpi_upd_wand H t Φ Ψ) $$ [Hwand] Hwp
  iintro %r Hupd
  imod Hupd with Hupd
  imodintro
  ispecialize Hwand $$ %r
  iapply Hwand $$ Hupd

/-- Consequence for the Coq-style masked WPi. -/
theorem wpiMask_wand {GF : BundledGFunctors} [InvGS_gen hlc GF]
    {ε : Type u → Type v} {ρ : Type uρ} (H : IHandler GF ε)
    (mask : CoPset) (t : ITree ε ρ) (Φ Ψ : ρ → IProp GF) :
    ⊢ iprop((∀ r, Φ r -∗ Ψ r) -∗
      wpiMask H mask t Φ -∗ wpiMask H mask t Ψ) := by
  iintro Hwand Hwp
  unfold wpiMask
  iapply (fupd_wand_left
    (P := wpi H t (fun r => iprop(|={∅, mask}=> Φ r))))
  isplitl [Hwand]
  · iintro Hcore
    iapply (wpi_wand H t
      (fun r => iprop(|={∅, mask}=> Φ r))
      (fun r => iprop(|={∅, mask}=> Ψ r))) $$ [Hwand] Hcore
    iintro %r Hpost
    iapply (fupd_wand_left (P := Φ r))
    isplitl [Hwand]
    · iintro Hr
      ispecialize Hwand $$ %r
      iapply Hwand $$ Hr
    · iexact Hpost
  · iexact Hwp

end ProgramLogicCarte
