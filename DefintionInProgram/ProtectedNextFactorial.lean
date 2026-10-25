import DefintionInProgram.ProtectedNext
import DefintionInProgram.NextFactorialMonitor

namespace ProgramLogic.ProtectedNext.Factorial
open Iris Iris.BI Iris.OFE ITree ProgramLogicCarte
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    [Small.{0} FacTree] [GhostVarG GF (Shrink FacTree)]
variable (γ : GName)

omit [Small.{0} FacTree] in
/-- Only the first source segment is unfolded; no factorial result theorem. -/
theorem fac_zero_segment :
    Silent (fac 0) (vis (.inl (.bp (0 : Int))) (fun _ => (ret 1 : FacTree))) := by
  rw [fac, rec_unfold, facBody, ite_eq_right (by omega), recRun_vis]
  simp only [ite_true, recRun_ret]
  exact .refl _

/-- Client triple with a return-indexed terminal certificate. Each callback
receives the driver's half through a wand, checks agreement with its sole
fragment, and returns both halves at the actual source endpoint. -/
theorem fac_monitor_zero_indexed_wp :
    fragment (GF := GF) γ (fac 0) ⊢
      wpi (logicalH voidUbH (authority γ : FacTree → IProp GF)) (facMonitor 0)
        (fun r => iprop(fragment γ (ret r : FacTree) ∗ ⌜r = 1⌝)) := by
  iintro Hf
  unfold facMonitor
  rw [facMonitorSteps, wpi_vis]
  imodintro
  isimp only [logicalH]
  iintro %s Ha
  ihave %he := agreement γ s (fac 0) $$ [$Ha $Hf]
  subst s
  iapply silent_until voidUbH fac_zero_segment
  rw [wpiUntil_bp]
  isimp only [boundary]
  imod (ghostUpdate γ (fac 0) (ret 1)) $$ [$Ha $Hf] with ⟨Ha, Hf⟩
  imodintro
  iframe Ha
  rw [facMonitorSteps, wpi_vis]
  imodintro
  isimp only [logicalH]
  iintro %s Ha
  ihave %he := agreement γ s (ret 1 : FacTree) $$ [$Ha $Hf]
  subst s
  rw [wpiUntil_ret]
  isimp only [boundary]
  imodintro
  iframe Ha
  rw [wpi_ret]
  imodintro
  iframe Hf
  ipureintro
  rfl

/-- The requested genuine client triple: its only premise is one fragment,
not authority, a full token, a source WP, or a representation specification. -/
theorem fac_monitor_zero_wp :
    fragment (GF := GF) γ (fac 0) ⊢
      wpi (logicalH voidUbH (authority γ : FacTree → IProp GF)) (facMonitor 0)
        (fun _ => fragment γ (ret 1 : FacTree)) := by
  iintro Hf
  ihave Hmonitor := fac_monitor_zero_indexed_wp γ $$ Hf
  iapply (wpi_wand (logicalH voidUbH (authority γ : FacTree → IProp GF)) _) $$ [] Hmonitor
  iintro %r ⟨Hf, %hr⟩
  subst r
  iexact Hf

local instance : IHandler.Sequential (voidUbH : IHandlerBase (IProp GF) (VoidE + UbE)) := by
  unfold voidUbH
  infer_instance

/-- Simulation starts with exactly two compatible halves, not three. The
terminal fragment is transferred out of the monitor WP, never duplicated. -/
theorem fac_zero_source_wp :
    iprop(authority (GF := GF) γ (fac 0) ∗ fragment γ (fac 0)) ⊢
      wpi (voidUbH (PROP := IProp GF)) (breakpointInter (fac 0))
        (fun r => iprop(authority γ (ret r : FacTree) ∗ fragment γ (ret 1 : FacTree))) := by
  iintro ⟨Ha, Hf⟩
  ihave Hmonitor := fac_monitor_zero_indexed_wp γ $$ Hf
  ihave Hsource : wpi voidUbH (breakpointInter (fac 0))
      (fun r => iprop(authority γ (ret r : FacTree) ∗
        fragment γ (ret r : FacTree) ∗ ⌜r = 1⌝)) $$ [Ha Hmonitor]
  · iapply simUntil voidUbH (authority γ) (fac 0) (facMonitor 0)
      (fun r => iprop(fragment γ (ret r : FacTree) ∗ ⌜r = 1⌝))
      (by
        intro s r
        iintro ⟨Ha, Hf, _⟩
        iapply agreement γ s (ret r) $$ [$Ha $Hf]) $$ [$Ha $Hmonitor]
  iapply (wpi_wand voidUbH _) $$ [] Hsource
  iintro %r ⟨Ha, Hf, %hr⟩
  subst r
  iframe

/-- Recover the numerical source result by agreement after simulation. Both
halves survive; no strong source execution premise is assumed. -/
theorem fac_zero_simUntil :
    iprop(authority (GF := GF) γ (fac 0) ∗ fragment γ (fac 0)) ⊢
      wpi (voidUbH (PROP := IProp GF)) (breakpointInter (fac 0))
        (fun r => iprop(authority γ (ret 1 : FacTree) ∗
          fragment γ (ret 1 : FacTree) ∗ ⌜r = 1⌝)) := by
  iintro Hinitial
  ihave Hsource := fac_zero_source_wp γ $$ Hinitial
  iapply (wpi_wand voidUbH _) $$ [] Hsource
  iintro %r ⟨Ha, Hf⟩
  ihave %he := agreement γ (ret r : FacTree) (ret 1 : FacTree) $$ [$Ha $Hf]
  have hr : r = 1 := ITree.ret_inj he
  subst r
  iframe Ha Hf
  ipureintro
  rfl

/-- Allocate exactly one full share, split into the source and client halves.
This witnesses compatibility of the simulation's initial resources. -/
theorem fac_zero_alloc :
    ⊢@{IProp GF} |==> ∃ γ, authority γ (fac 0) ∗ fragment γ (fac 0) :=
  alloc (fac 0)

/-- End-to-end allocation followed by simulation, with no external ownership
premise that could hide an inconsistent additional half. -/
theorem fac_zero_alloc_simUntil :
    ⊢@{IProp GF} |={∅}=> ∃ γ,
      wpi voidUbH (breakpointInter (fac 0))
        (fun r => iprop(authority γ (ret 1 : FacTree) ∗
          fragment γ (ret 1 : FacTree) ∗ ⌜r = 1⌝)) := by
  istart
  imod fac_zero_alloc with ⟨%γ, Ha, Hf⟩
  imodintro
  iexists γ
  iapply fac_zero_simUntil γ $$ [$Ha $Hf]

end ProgramLogic.ProtectedNext.Factorial
