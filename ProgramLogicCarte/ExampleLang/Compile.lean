import ITree.Recursion
import ProgramLogicCarte.ExampleLang.Syntax
import ProgramLogicCarte.Threadpool
import ProgramLogicCarte.State
import ProgramLogicCarte.ExampleLang.Heap
import ProgramLogicCarte.Choice

/-! The complete event structure of `src/examplelang/lang.v`. -/
namespace ProgramLogicCarte.ExampleLang
open ITree

inductive ExampleE : Type → Type 1 where
  | threadpool {α : Type} (event : ThreadpoolE α) : ExampleE α
  | undefined {α : Type} (event : UbE α) : ExampleE α
  | heap {α : Type} (event : StateE ExampleHeap α) : ExampleE α
  | demonic {α : Type} (event : DemonicE α) : ExampleE α

abbrev SourceE : Type → Type 1 := CallE Expr Value + ExampleE

def yieldIfNotVal : Expr → ITree SourceE (ULift Unit)
  | .val _ => ret (.up ())
  | _ => trigger (.inr (.threadpool .yield))

def sourceUb {ρ : Type} : ITree SourceE ρ :=
  vis (.inr (.undefined .crash)) (fun answer => nomatch answer.down)

def someOrUb {ρ : Type} : Option ρ → ITree SourceE ρ
  | some value => ret value
  | none => sourceUb

def getHeap : ITree SourceE (ExampleHeap) := trigger (.inr (.heap .get))
def setHeap (heap : ExampleHeap) : ITree SourceE (ULift Unit) :=
  trigger (.inr (.heap (.set heap)))

def alloc (value : Value) : ITree SourceE Int :=
  ITree.bind getHeap fun heap =>
  ITree.bind (setHeap (heap.write heap.fresh (some value))) fun _ =>
  ret heap.fresh

def loadOrUb (location : Int) : ITree SourceE Value :=
  ITree.bind getHeap fun heap => someOrUb (heap.read location)

def storeOrUb (location : Int) (value : Value) : ITree SourceE Value :=
  ITree.bind getHeap fun heap =>
  ITree.bind (setHeap (heap.write location (some value))) fun _ =>
  someOrUb (heap.read location)

def Value.toLoc? : Value → Option Int
  | .lit (.loc location) => some location
  | _ => none

/-- Coq's `compile_expr'`, including yields after non-values and recursive calls. -/
def compileExpr' : Expr → ITree SourceE Value
  | .var _ => sourceUb
  | .val value => ret value
  | .lam binder body => ret (.lam binder body)
  | .app fn arg =>
      ITree.bind (compileExpr' fn) fun function =>
      ITree.bind (yieldIfNotVal fn) fun _ =>
      ITree.bind (compileExpr' arg) fun argument =>
      ITree.bind (yieldIfNotVal arg) fun _ =>
      ITree.bind (someOrUb function.toLam?) fun (binder, body) =>
      let body := substBinder binder argument body
      ITree.bind (yieldIfNotVal body) fun _ =>
      ITree.call body
  | .plus left right =>
      ITree.bind (compileExpr' left) fun leftValue =>
      ITree.bind (yieldIfNotVal left) fun _ =>
      ITree.bind (compileExpr' right) fun rightValue =>
      ITree.bind (yieldIfNotVal right) fun _ =>
      ITree.bind (someOrUb leftValue.toInt?) fun leftInt =>
      ITree.bind (someOrUb rightValue.toInt?) fun rightInt =>
      ret (.lit (.int (leftInt + rightInt)))
  | .ite test yes no =>
      ITree.bind (compileExpr' test) fun testValue =>
      ITree.bind (yieldIfNotVal test) fun _ =>
      ITree.bind (someOrUb testValue.toInt?) fun testInt =>
      if testInt = 0 then
        ITree.bind (yieldIfNotVal no) fun _ => compileExpr' no
      else
        ITree.bind (yieldIfNotVal yes) fun _ => compileExpr' yes
  | .ref value =>
      ITree.bind (compileExpr' value) fun result =>
      ITree.bind (yieldIfNotVal value) fun _ =>
      ITree.bind (alloc result) fun location =>
      ret (.lit (.loc location))
  | .load address =>
      ITree.bind (compileExpr' address) fun addressValue =>
      ITree.bind (someOrUb addressValue.toLoc?) fun location =>
      loadOrUb location
  | .store address value =>
      ITree.bind (compileExpr' address) fun addressValue =>
      ITree.bind (compileExpr' value) fun newValue =>
      ITree.bind (someOrUb addressValue.toLoc?) fun location =>
      storeOrUb location newValue
  | .pickInt =>
      ITree.bind (trigger (.inr (.demonic (.choose Int 0)))) fun value =>
      ret (.lit (.int value))
  | .spawn body =>
      ITree.bind (trigger (.inr (.threadpool .fork))) fun thread =>
      ITree.bind (match thread with
        | .current => ret (.up ())
        | .spawned =>
            ITree.bind (compileExpr' body) fun _ =>
            ITree.bind (yieldIfNotVal body) fun _ =>
            (vis (.inr (.threadpool .kill)) fun answer => nomatch answer.down :
              ITree SourceE (ULift.{0,0} Unit))) fun _ =>
      ret (.lit (.int 0))

/-- Interpret recursive calls without a fuel bound. -/
def compileExpr (expr : Expr) : ITree ExampleE Value :=
  ITree.rec compileExpr' expr

/-- Values compile to a return, including recursive-call interpretation. -/
@[simp] theorem compileExpr_val (value : Value) :
    compileExpr (.val value) = ret value :=
  ITree.rec_ret compileExpr' (.val value) value rfl

/-- A source lambda is already a value and emits no effects. -/
@[simp] theorem compileExpr_lam (binder : Binder) (body : Expr) :
    compileExpr (.lam binder body) = ret (.lam binder body) :=
  ITree.rec_ret compileExpr' (.lam binder body) (.lam binder body) rfl

/-- The closed integer-addition example has no visible effects. -/
@[simp] theorem compileExpr_plus_values (left right : Int) :
    compileExpr (.plus (.val (.lit (.int left))) (.val (.lit (.int right)))) =
      ret (.lit (.int (left + right))) := by
  apply ITree.rec_ret
  simp only [compileExpr', yieldIfNotVal]
  repeat rw [ITree.bind_ret]
  simp only [Value.toInt?, someOrUb]
  repeat rw [ITree.bind_ret]

/-- A closed beta-reduction executes the recursive call and resumes its continuation. -/
theorem compileExpr_beta (value : Value) :
    compileExpr (.app (.val (.lam (.named "x") (.var "x"))) (.val value)) =
      tau (tau (ret value)) := by
  have hbody :
      compileExpr' (.app (.val (.lam (.named "x") (.var "x"))) (.val value)) =
        ITree.call (.val value) := by
    simp only [compileExpr', yieldIfNotVal]
    repeat rw [ITree.bind_ret]
    simp only [Value.toLam?, someOrUb, substBinder]
    repeat rw [ITree.bind_ret]
    simp [subst]
    change ITree.bind (ITree.ret (ULift.up ())) (fun _ => ITree.call (Expr.val value)) = ITree.call (Expr.val value)
    rw [ITree.bind_ret]
  unfold compileExpr ITree.rec
  rw [hbody]
  simp only [ITree.call, ITree.trigger, ITree.recState_call]
  simp only [compileExpr', ITree.recState_ret_cons, ITree.recState_ret_nil]

/-- A conditional on an integer literal selects exactly one branch. -/
theorem compileExpr_if_values (test : Int) (yes no : Value) :
    compileExpr (.ite (.val (.lit (.int test))) (.val yes) (.val no)) =
      ret (if test = 0 then no else yes) := by
  apply ITree.rec_ret
  simp only [compileExpr', yieldIfNotVal]
  repeat rw [ITree.bind_ret]
  simp only [Value.toInt?, someOrUb]
  repeat rw [ITree.bind_ret]
  by_cases h : test = 0
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]

/-- Ref on a value emits exactly one allocation. -/
theorem compileExpr'_ref_value (value : Value) :
    compileExpr' (.ref (.val value)) =
      ITree.bind (alloc value) (fun location => ret (.lit (.loc location))) := by
  simp only [compileExpr', yieldIfNotVal]
  rw [ITree.bind_ret, ITree.bind_ret]

/-- Load on a location value emits exactly one heap read. -/
theorem compileExpr'_load_value (location : Int) :
    compileExpr' (.load (.val (.lit (.loc location)))) = loadOrUb location := by
  simp only [compileExpr']
  rw [ITree.bind_ret]
  simp only [Value.toLoc?, someOrUb]
  rw [ITree.bind_ret]

/-- Store on two values emits a heap read and write, returning the old value. -/
theorem compileExpr'_store_values (location : Int) (value : Value) :
    compileExpr' (.store (.val (.lit (.loc location))) (.val value)) =
      storeOrUb location value := by
  simp only [compileExpr']
  repeat rw [ITree.bind_ret]
  simp only [Value.toLoc?, someOrUb]
  rw [ITree.bind_ret]

/-- `Load` does not yield after a non-value address in the Coq compiler.
The invalid address immediately emits undefined behavior. -/
theorem compileExpr'_load_lam_ub :
    compileExpr' (.load (.lam .anon .pickInt)) = (sourceUb : ITree SourceE Value) := by
  simp only [compileExpr', ITree.bind_ret, Value.toLoc?, someOrUb]
  simp only [sourceUb, ITree.bind_vis]
  congr 1
  funext answer
  exact Empty.elim answer.down

/-- The source choice remains visible after recursive-call interpretation. -/
theorem compileExpr_pickInt :
    compileExpr .pickInt =
      vis (ExampleE.demonic (.choose Int 0)) (fun n => ret (.lit (.int n))) := by
  have hbody :
      compileExpr' .pickInt =
        vis (SumE.inr (ExampleE.demonic (.choose Int 0)))
          (fun n => ret (.lit (.int n))) := by
    simp only [compileExpr', trigger, ITree.bind_vis, ITree.bind_ret]
  unfold compileExpr ITree.rec
  rw [hbody, ITree.recState_vis]
  simp only [ITree.recState_ret_nil]

end ProgramLogicCarte.ExampleLang
