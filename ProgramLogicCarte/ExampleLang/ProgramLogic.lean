import ProgramLogicCarte.ExampleLang.Compile
import ProgramLogicCarte.WpiStructural

/-! Logical interpretation of the ExampleLang effect signature. -/
namespace ProgramLogicCarte.ExampleLang
open Iris Iris.BI Iris.OFE ITree

def exampleH {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF (ExampleHeap)] : IHandler GF ExampleE where
  handle e Φ spawned := match e with
    | .threadpool event => threadpoolH.handle event Φ spawned
    | .undefined event => ubH.handle event Φ spawned
    | .heap event => (stateH (ExampleHeap)).handle event Φ spawned
    | .demonic event => demonicH.handle event Φ spawned
  mono e := by
    cases e with
    | threadpool event => exact threadpoolH.mono event
    | undefined event => exact ubH.mono event
    | heap event => exact (stateH (ExampleHeap)).mono event
    | demonic event => exact demonicH.mono event
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    cases e with
    | threadpool event => exact threadpoolH.ne event hΦ hspawned
    | undefined event => exact ubH.ne event hΦ hspawned
    | heap event => exact (stateH (ExampleHeap)).ne event hΦ hspawned
    | demonic event => exact demonicH.ne event hΦ hspawned

/-- Yield is available in the composed ExampleLang handler at the full mask. -/
theorem wpi_example_yield {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (Φ : ULift Unit → IProp GF) :
    Φ (.up ()) ⊢
      wpiMask exampleH ⊤
        (ITree.trigger (ExampleE.threadpool ThreadpoolE.yield)) Φ := by
  simpa only [wpiMask, yield, ITree.trigger, wpi_vis, wpi_ret,
    exampleH, threadpoolH] using (wpi_mask_yield Φ)

/-- The ExampleLang specialization of Coq's polymorphic
`yield_if_not_val` helper. -/
def yieldIfNotValExample : Expr → ITree ExampleE (ULift Unit)
  | .val _ => ret (.up ())
  | _ => ITree.trigger (.threadpool .yield)

/-- Coq's `wpi_yield_if_not_val` at the full mask. -/
theorem wpi_yield_if_not_val {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (expr : Expr) (Φ : ULift Unit → IProp GF) :
    Φ (.up ()) ⊢ wpiMask exampleH ⊤ (yieldIfNotValExample expr) Φ := by
  cases expr <;> simp only [yieldIfNotValExample]
  · exact wpiMask_ret exampleH ⊤ (.up ()) Φ
  all_goals exact wpi_example_yield Φ

/-- Exact masked ExampleLang WP used by Coq `wp_example`. -/
def wpExampleMask {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (mask : CoPset) (expr : Expr)
    (Φ : Value → IProp GF) : IProp GF :=
  wpiMask exampleH mask (compileExpr expr) Φ

/-- Coq's value rule holds under any mask. -/
theorem wp_mask_val {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (mask : CoPset) (value : Value)
    (Φ : Value → IProp GF) :
    Φ value ⊢ wpExampleMask mask (.val value) Φ := by
  rw [wpExampleMask, compileExpr_val, wpiMask, wpi_ret]
  istart
  iintro H
  iapply (fupd_mono (fupd_intro (E := (∅ : CoPset))))
  iapply fupd_mask_intro_subseteq Std.LawfulSet.empty_subset
  iexact H

/-- Coq's `wp_wand` for the masked ExampleLang WP. -/
theorem wp_mask_wand {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (mask : CoPset) (expr : Expr)
    (Φ Ψ : Value → IProp GF) :
    ⊢ iprop((∀ value, Φ value -∗ Ψ value) -∗
      wpExampleMask mask expr Φ -∗ wpExampleMask mask expr Ψ) := by
  exact wpiMask_wand exampleH mask (compileExpr expr) Φ Ψ

/-- Coq's `wp_frame` for the masked ExampleLang WP. -/
theorem wp_mask_frame {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (P : IProp GF) (mask : CoPset)
    (expr : Expr) (Φ : Value → IProp GF) :
    ⊢ iprop(P -∗ wpExampleMask mask expr Φ -∗
      wpExampleMask mask expr (fun value => iprop(P ∗ Φ value))) := by
  iintro HP Hwp
  iapply (wp_mask_wand mask expr Φ (fun value => iprop(P ∗ Φ value))) $$ [HP] Hwp
  iintro %value HΦ
  iframe

/-- A source lambda is a value under every invariant mask. -/
theorem wp_mask_lam {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (mask : CoPset)
    (binder : Binder) (body : Expr) (Φ : Value → IProp GF) :
    Φ (.lam binder body) ⊢ wpExampleMask mask (.lam binder body) Φ := by
  rw [wpExampleMask, compileExpr_lam]
  exact wpiMask_ret exampleH mask (.lam binder body) Φ

/-- Closed integer addition has the same masked WP as its result. -/
theorem wp_mask_plus {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (mask : CoPset) (left right : Int)
    (Φ : Value → IProp GF) :
    Φ (.lit (.int (left + right))) ⊢
      wpExampleMask mask
        (.plus (.val (.lit (.int left))) (.val (.lit (.int right)))) Φ := by
  simpa only [wpExampleMask, compileExpr_val, compileExpr_plus_values] using
    wp_mask_val mask (.lit (.int (left + right))) Φ

/-- Closed conditional selection is valid under every mask. -/
theorem wp_mask_if_values {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (mask : CoPset) (test : Int)
    (yes no : Value) (Φ : Value → IProp GF) :
    Φ (if test = 0 then no else yes) ⊢
      wpExampleMask mask (.ite (.val (.lit (.int test))) (.val yes) (.val no)) Φ := by
  simpa only [wpExampleMask, compileExpr_val, compileExpr_if_values] using
    wp_mask_val mask (if test = 0 then no else yes) Φ

/-- Closed beta reduction remains valid under every mask; its two
administrative tau steps do not affect the masked WP. -/
theorem wp_mask_beta {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (mask : CoPset) (value : Value)
    (Φ : Value → IProp GF) :
    Φ value ⊢ wpExampleMask mask
      (.app (.val (.lam (.named "x") (.var "x"))) (.val value)) Φ := by
  rw [wpExampleMask, compileExpr_beta, wpiMask, ← wpi_tau, ← wpi_tau]
  simpa only [wpExampleMask, compileExpr_val, wpiMask] using
    wp_mask_val mask value Φ

/-- Coq's `wp_pick_int` rule under an arbitrary mask. -/
theorem wp_mask_pick_int {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (mask : CoPset) (Φ : Value → IProp GF) :
    iprop(∀ n : Int, Φ (.lit (.int n))) ⊢
      wpExampleMask mask .pickInt Φ := by
  rw [wpExampleMask, compileExpr_pickInt, wpiMask, wpi_vis]
  istart
  iintro HAll
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  imodintro
  isimp only [exampleH, demonicH]
  iintro %n
  rw [wpi_ret]
  imodintro
  iapply (fupd_wand_left (P := (emp : IProp GF)))
  isplitl [HAll]
  · iintro _
    ispecialize HAll $$ %n
    iexact HAll
  · iexact Hclose

def wpExample {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF (ExampleHeap)] (expr : Expr) (Φ : Value → IProp GF) : IProp GF :=
  wpi exampleH (compileExpr expr) Φ

/-- The source-language value rule. -/
theorem wp_val {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF (ExampleHeap)] (value : Value) (Φ : Value → IProp GF) :
    Φ value ⊢ wpExample (.val value) Φ := by
  rw [wpExample, compileExpr_val, wpi_ret]
  istart
  iintro H
  imodintro
  iexact H

/-- The source-language rule for adding two integer literals. -/
theorem wp_plus {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF (ExampleHeap)] (left right : Int) (Φ : Value → IProp GF) :
    Φ (.lit (.int (left + right))) ⊢
      wpExample (.plus (.val (.lit (.int left))) (.val (.lit (.int right)))) Φ := by
  rw [wpExample, compileExpr_plus_values, wpi_ret]
  istart
  iintro H
  imodintro
  iexact H

/-- An application whose body is the bound variable returns its argument. -/
theorem wp_beta {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF (ExampleHeap)] (value : Value) (Φ : Value → IProp GF) :
    Φ value ⊢ wpExample
      (.app (.val (.lam (.named "x") (.var "x"))) (.val value)) Φ := by
  rw [wpExample, compileExpr_beta]
  rw [← wpi_tau, ← wpi_tau, wpi_ret]
  istart
  iintro H
  imodintro
  iexact H

/-- The source-language rule for a conditional with value branches. -/
theorem wp_if_values {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF (ExampleHeap)] (test : Int) (yes no : Value)
    (Φ : Value → IProp GF) :
    Φ (if test = 0 then no else yes) ⊢
      wpExample (.ite (.val (.lit (.int test))) (.val yes) (.val no)) Φ := by
  rw [wpExample, compileExpr_if_values, wpi_ret]
  istart
  iintro H
  imodintro
  iexact H

/-- Demonically chosen integers require the postcondition for every integer. -/
theorem wp_pick_int {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [StateInterp GF ExampleHeap] (Φ : Value → IProp GF) :
    iprop(∀ n : Int, Φ (.lit (.int n))) ⊢ wpExample .pickInt Φ := by
  rw [wpExample, compileExpr_pickInt, wpi_vis]
  istart
  iintro HAll
  imodintro
  isimp only [exampleH, demonicH]
  iintro %n
  rw [wpi_ret]
  imodintro
  ispecialize HAll $$ %n
  iexact HAll

end ProgramLogicCarte.ExampleLang
