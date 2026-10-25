import DefintionInProgram.NextSegment
import IrisUtil.Fractional
import Mathlib.Logic.Small.Defs

/-!
# State-passing logical interpretation of protected next

The driver owns one half of the source state, the client the other half.
`logicalH` temporarily supplies the driver half through a wand, as a state
handler does. Its segment WP is indexed by the actual input source, and its
boundary restores authority at the actual successor. No extra fragment is
framed by the driver.

This is not syntactic confinement of ghost updates: inside the callback both
halves can be combined and updated arbitrarily. Soundness concerns the boundary
and the source WP, not transient ghost states. Returning from the monitor alone
is not evidence of source termination; simulation requires a return-indexed
fragment in the monitor postcondition. All WPs here use the empty mask; a
nonempty invariant mask must be opened/restored with the usual masked WP API.
-/
namespace ProgramLogic.ProtectedNext
open Iris Iris.BI Iris.OFE ITree ProgramLogicCarte
universe u v w

abbrev Tree := NextToken.Tree

/-- Only matching endpoints are accepted; `next` cannot return and `finish`
cannot cross a breakpoint. Authority records the actual segment successor. -/
def boundary {PROP : Type w} [BI PROP]
    {ι ρ : Type u} {ε : Type u → Type (max u v)}
    (authority : Tree ι ρ ε → PROP) {α : Type u}
    (e : NextE.{u, v} ρ α) (Ψ : α → PROP)
    (result : BreakpointResult ι ε ρ) : PROP :=
  match e, result with
  | .next, .stopped _ rest => iprop(authority rest ∗ Ψ (.up ()))
  | .finish, .returned r => iprop(authority (ret r) ∗ Ψ r)
  | _, _ => iprop(False)

/-- Standard state-passing callback: the source index is universally quantified,
not chosen by the client after receiving authority. Spawned branches are unused. -/
def logicalH {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ι ρ : Type u} {ε : Type u → Type (max u v)}
    (H : IHandlerBase PROP ε) (authority : Tree ι ρ ε → PROP) :
    IHandlerBase PROP (NextE.{u, v} ρ) where
  handle e Ψ _ := iprop(∀ s : Tree ι ρ ε,
    authority s -∗ wpiUntil H s (boundary authority e Ψ))
  mono e := by
    intro Ψ Ψ' spawned spawned'
    iintro HΨ _ Hop %s Ha
    ispecialize Hop $$ %s Ha
    isimp only [wpiUntil] at Hop
    unfold wpiUntil
    iapply (wpi_wand H _) $$ [HΨ] Hop
    iintro %result Hr
    cases e <;> cases result
    all_goals isimp only [boundary] at Hr
    all_goals isimp only [boundary]
    all_goals first
      | (icases Hr with ⟨Ha, Hcont⟩; iframe Ha; iapply HΨ $$ Hcont)
      | (iexact Hr)
  ne := by
    intro n α e Ψ₁ Ψ₂ spawned₁ spawned₂ hΨ _
    exact forall_ne fun s => wand_ne.ne .rfl <|
      NonExpansive.ne (f := wpiUntil H s) (by
        intro result
        cases e <;> cases result <;> simp only [boundary]
        all_goals first | exact sep_ne.ne .rfl (hΨ _) | exact .rfl)

instance logicalHSequential {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ι ρ : Type u} {ε : Type u → Type (max u v)}
    (H : IHandlerBase PROP ε) (authority : Tree ι ρ ε → PROP) :
    IHandler.Sequential (logicalH H authority) where
  sequential _ _ _ := .rfl

/-- Structural evidence for finite effect-free segments, used only by clients.
The handler and simulation also support ordinary effects through `H`. -/
inductive Silent {ι ρ : Type u} {ε : Type u → Type (max u v)} :
    Tree ι ρ ε → Tree ι ρ ε → Prop where
  | refl (t) : Silent t t
  | tau {s t} : Silent s t → Silent (ITree.tau s) t

theorem silent_until {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ι ρ : Type u} {ε : Type u → Type (max u v)}
    (H : IHandlerBase PROP ε) {s t : Tree ι ρ ε} (h : Silent s t)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntil H t Φ ⊢ wpiUntil H s Φ := by
  induction h with
  | refl => exact entails_refl
  | tau _ ih => rw [wpiUntil_tau]; exact ih

/-- Generic WP simulation with an explicit terminal bridge. The bridge is
linear and is threaded through segments, not duplicated at each callback. -/
private theorem simulate {PROP : Type w} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]
    {ι ρ : Type u} {ε : Type u → Type (max u v)}
    (H : IHandlerBase PROP ε) [IHandler.Sequential H]
    (authority : Tree ι ρ ε → PROP)
    (source : Tree ι ρ ε) (monitor : ITree (NextE.{u, v} ρ) ρ)
    (post Φ : ρ → PROP) :
    iprop(authority source ∗ wpi (logicalH H authority) monitor post ∗
      (∀ r, post r -∗ ∀ t : Tree ι ρ ε, authority t -∗
        wpi H (breakpointInter t) Φ)) ⊢
      wpi H (breakpointInter source) Φ := by
  let P : WpiState PROP (NextE.{u, v} ρ) ρ → PROP := fun st =>
    iprop(∀ s : Tree ι ρ ε, authority s -∗
      (∀ r, st.2 r -∗ ∀ t : Tree ι ρ ε, authority t -∗
        wpi H (breakpointInter t) Φ) -∗ wpi H (breakpointInter s) Φ)
  have : NonExpansive P := ⟨by
    intro n a b hab
    exact forall_ne fun s => wand_ne.ne .rfl <| wand_ne.ne
      (forall_ne fun r => wand_ne.ne (hab.2 r) .rfl) .rfl⟩
  iintro ⟨Ha, Hmonitor, Hpost⟩
  ihave Hgen : iprop(∀ st : WpiState PROP (NextE.{u, v} ρ) ρ,
      wpi (logicalH H authority) st.1.car st.2 -∗ P st) $$ []
  · iapply (wpi_iter (logicalH H authority) P)
    iintro !> %st HF
    rcases st with ⟨⟨tree⟩, post⟩
    isimp only [P]
    iintro %s Ha Hpost
    apply tree.dMatchOn
    · intro r heq
      subst tree
      isimp only [wpiF', wpiF, dest_ret] at HF
      rw [wpi_tau H (breakpointInter s), wpi_tau_step]
      imod HF with HF
      imodintro
      iapply Hpost $$ HF %s Ha
    · intro child heq
      subst tree
      isimp only [wpiF', wpiF, dest_tau] at HF
      rw [wpi_tau H (breakpointInter s), wpi_tau_step]
      imod HF with HF
      isimp only [P, fin1Const] at HF
      imodintro
      iapply HF $$ %s Ha Hpost
    · intro α e k heq
      subst tree
      isimp only [wpiF', wpiF, dest_vis, logicalH] at HF
      rw [wpi_tau H (breakpointInter s), wpi_tau_step]
      imod HF with HF
      ispecialize HF $$ %s Ha
      isimp only [wpiUntil] at HF
      ihave Hjoined : wpi H (breakpointInter s) Φ $$ [HF Hpost]
      · iapply wpiUntil_rejoin
        unfold wpiUntil
        iapply (wpi_upd_wand H _) $$ [Hpost] HF
        iintro %result Hr
        imod Hr with Hr
        cases e <;> cases result
        all_goals isimp only [boundary] at Hr
        all_goals isimp only [boundary]
        · iapply false_elim; iexact Hr
        · icases Hr with ⟨Ha, Hcont⟩
          isimp only [P] at Hcont
          imodintro
          iapply Hcont $$ %_ Ha Hpost
        · icases Hr with ⟨Ha, Hcont⟩
          isimp only [P] at Hcont
          ihave Hret := Hcont $$ %(ret _) Ha Hpost
          isimp only [breakpointInter_return, wpi_ret] at Hret
          imod Hret with Hret
          imodintro
          iexact Hret
        · iapply false_elim; iexact Hr
      imodintro
      iexact Hjoined
  ispecialize Hgen $$ %(⟨⟨monitor⟩, post⟩ : WpiState PROP (NextE.{u, v} ρ) ρ) Hmonitor
  isimp only [P] at Hgen
  iapply Hgen $$ %source Ha Hpost

/-- The terminal contract must identify the source as returning the monitor's
result. A return-indexed fragment supplies this contract by agreement. Without
it, an immediately returning monitor would make the statement false.

The output is exactly authority plus the client's postcondition: the driver
does not retain or manufacture a second fragment. -/
theorem simUntil {PROP : Type w} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]
    {ι ρ : Type u} {ε : Type u → Type (max u v)}
    (H : IHandlerBase PROP ε) [IHandler.Sequential H]
    (authority : Tree ι ρ ε → PROP)
    (source : Tree ι ρ ε) (monitor : ITree (NextE.{u, v} ρ) ρ) (Ψ : ρ → PROP)
    (terminal : ∀ s r, iprop(authority s ∗ Ψ r) ⊢ iprop(⌜s = ret r⌝)) :
    iprop(authority source ∗ wpi (logicalH H authority) monitor Ψ) ⊢
      wpi H (breakpointInter source) (fun r => iprop(authority (ret r) ∗ Ψ r)) := by
  iintro ⟨Ha, Hmonitor⟩
  iapply simulate H authority source monitor _ _ $$ [$Ha $Hmonitor]
  iintro %r HΨ %s Ha
  ihave %he := terminal s r $$ [$Ha $HΨ]
  subst s
  rw [breakpointInter_return, wpi_ret]
  imodintro
  iframe

section Ghost
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    {ι ρ : Type u} {ε : Type u → Type (max u v)}
    [Small.{0} (Tree ι ρ ε)] [GhostVarG GF (Shrink (Tree ι ρ ε))]

noncomputable def authority (γ : GName) (t : Tree ι ρ ε) : IProp GF :=
  ghost_var γ (.own (1 : Qp).half) (equivShrink (Tree ι ρ ε) t)

noncomputable def fragment (γ : GName) (t : Tree ι ρ ε) : IProp GF :=
  ghost_var γ (.own (1 : Qp).half) (equivShrink (Tree ι ρ ε) t)

/-- Raw joint update, intentionally unrestricted. Segment legality comes from
`logicalH`, not from a false claim of ghost-update confinement. -/
theorem ghostUpdate (γ : GName) (s t : Tree ι ρ ε) :
    iprop(authority (GF := GF) γ s ∗ fragment γ s) ⊢
    iprop(|={∅}=> authority γ t ∗ fragment γ t) := by
  unfold authority fragment
  iintro ⟨Ha, Hf⟩
  imod (ghost_var_update_halves (equivShrink (Tree ι ρ ε) t)) $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe

theorem alloc (t : Tree ι ρ ε) :
    ⊢@{IProp GF} |==> ∃ γ, authority γ t ∗ fragment γ t := by
  istart
  imod (ghost_var_alloc (equivShrink (Tree ι ρ ε) t)) with ⟨%γ, H⟩
  iexists γ
  unfold authority fragment
  imodintro
  have split := ghost_var_split (GF := GF) γ (equivShrink (Tree ι ρ ε) t)
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at split
  icases split $$ H with ⟨Ha, Hf⟩
  iframe

theorem agreement (γ : GName) (s t : Tree ι ρ ε) :
    iprop(authority (GF := GF) γ s ∗ fragment γ t) ⊢ iprop(⌜s = t⌝) := by
  unfold authority fragment
  iintro ⟨Ha, Hf⟩
  ihave %he := ghost_var_agree $$ Ha Hf
  ipureintro
  exact (equivShrink (Tree ι ρ ε)).injective he

/-- Stability while the authority half remains framed outside the callback. -/
theorem framed_agreement (γ : GName) (s t : Tree ι ρ ε) :
    iprop(authority (GF := GF) γ s ∗ (|={∅}=> fragment γ t)) ⊢
    iprop(|={∅}=> ⌜s = t⌝ ∗ authority γ s ∗ fragment γ t) := by
  iintro ⟨Ha, Hf⟩
  imod Hf with Hf
  ihave %he := agreement γ s t $$ [$Ha $Hf]
  imodintro
  iframe
  ipureintro
  exact he
end Ghost
end ProgramLogic.ProtectedNext
