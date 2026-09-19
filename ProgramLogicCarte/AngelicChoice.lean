import ProgramLogicCarte.Wpi
import ITree.UpToTaus

/-! Angelic nondeterminism (`src/angelic_choice.v`). -/

namespace ProgramLogicCarte

open Iris Iris.BI ITree

universe u

/-- An event whose branch may be chosen angelically. -/
inductive AngelicE : Type u → Type (u + 1) where
  | choose (α : Type u) : AngelicE α

def angelicChoice (α : Type u) : ITree AngelicE α :=
  trigger (.choose α)

/-- The angelic handler requires only one successful continuation. -/
def angelicH {GF : BundledGFunctors} : IHandler GF AngelicE where
  handle e Φ _ := match e with
    | .choose _ => iprop(∃ x, Φ x)
  mono e := by
    cases e
    intro Φ Φ' spawned spawned'
    istart
    iintro HΦ _ HSome
    icases HSome with ⟨%x, Hx⟩
    iexists x
    iapply HΦ
    iexact Hx
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    cases e
    exact exists_ne hΦ

instance angelicHSequential {GF : BundledGFunctors} :
    IHandler.Sequential (angelicH : IHandler GF AngelicE) where
  sequential e Φ spawned := by
    cases e
    exact .rfl

/-- WP rule selecting a witness for an angelic choice. -/
theorem wpi_angelicChoice {GF : BundledGFunctors} [InvGS_gen hlc GF]
    (α : Type u) (chosen : α) (Φ : α → IProp GF) :
    Φ chosen ⊢ wpi angelicH (angelicChoice α) Φ := by
  rw [angelicChoice, trigger, wpi_vis]
  istart
  iintro Hchosen
  imodintro
  isimp only [angelicH]
  iexists chosen
  rw [wpi_ret]
  imodintro
  iexact Hchosen

end ProgramLogicCarte
