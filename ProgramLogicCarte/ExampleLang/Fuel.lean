import ProgramLogicCarte.ExampleLang.Syntax
import ProgramLogicCarte.Choice
import ProgramLogicCarte.Interpreter

/-!
# Fuelled compiler for ExampleLang

The Coq `compile_expr` is defined through the `callE` recursion effect.  Until
the general recursive interpreter is ported, this module gives its executable
finite approximation.  Every recursive source call consumes one unit of fuel;
exhaustion and constructs owned by the not-yet-ported heap/thread-pool back
ends return `none`.  This keeps the finite approximation executable while the
full `UbE`/heap/thread-pool composition is being ported.
-/

namespace ProgramLogicCarte.ExampleLang

open ITree

abbrev CoreE : Type → Type 1 := DemonicE + (VoidE : Type → Type 1)

private def failed : ITree CoreE (Option Value) := ret none

private def chooseInt : ITree CoreE Int :=
  vis (SumE.inl (.choose Int 0)) ret

/-- Finite approximation of the upstream `compile_expr`. -/
def compileFuel : Nat → Expr → ITree CoreE (Option Value)
  | 0, _ => failed
  | _fuel + 1, .var _ => failed
  | _fuel + 1, .val value => ret (some value)
  | _fuel + 1, .lam binder body => ret (some (.lam binder body))
  | fuel + 1, .app fn arg =>
      ITree.bind (compileFuel fuel fn) fun
      | some fnValue => ITree.bind (compileFuel fuel arg) fun
        | some argValue => match fnValue.toLam? with
          | some (binder, body) => compileFuel fuel (substBinder binder argValue body)
          | none => failed
        | none => failed
      | none => failed
  | fuel + 1, .plus left right =>
      ITree.bind (compileFuel fuel left) fun
      | some leftValue => ITree.bind (compileFuel fuel right) fun
        | some rightValue => match leftValue.toInt?, rightValue.toInt? with
          | some leftInt, some rightInt => ret (some (.lit (.int (leftInt + rightInt))))
          | _, _ => failed
        | none => failed
      | none => failed
  | fuel + 1, .ite test yes no =>
      ITree.bind (compileFuel fuel test) fun
      | some testValue => match testValue.toInt? with
        | some testInt => if testInt = 0 then compileFuel fuel no else compileFuel fuel yes
        | none => failed
      | none => failed
  | _fuel + 1, .pickInt =>
      ITree.bind chooseInt fun value => ret (some (.lit (.int value)))
  | _fuel + 1, .ref _ => failed
  | _fuel + 1, .load _ => failed
  | _fuel + 1, .store _ _ => failed
  | _fuel + 1, .spawn _ => failed

@[simp]
theorem compileFuel_zero (expr : Expr) : compileFuel 0 expr = failed :=
  rfl

private def one : Value := .lit (.int 1)
private def two : Value := .lit (.int 2)

example : compileFuel 3 (.plus (.val one) (.val two)) =
    ret (some (.lit (.int 3) : Value)) := by
  simp only [compileFuel]
  rw [ITree.bind_ret]
  simp only
  rw [ITree.bind_ret]
  rfl

example : compileFuel 3 (.ite (.val (.lit (.int 0))) (.val one) (.val two)) = ret (some two) := by
  simp only [compileFuel]
  rw [ITree.bind_ret]
  rfl

example : compileFuel 4
    (.app (.lam (.named "x") (.plus (.var "x") (.val one))) (.val two)) =
    ret (some (.lit (.int 3) : Value)) := by
  simp only [compileFuel, Value.toLam?, substBinder]
  rw [ITree.bind_ret]
  simp only
  rw [ITree.bind_ret]
  simp only [subst, ite_true, compileFuel]
  rw [ITree.bind_ret]
  simp only
  rw [ITree.bind_ret]
  rfl

/-- The source-level choice event survives compilation and is resolved by the
concrete demonic interpreter. -/
example : demonicIfn (compileFuel 1 .pickInt) =
    tau (ret (some (.lit (.int 0) : Value)) : ITree (VoidE : Type → Type 1) (Option Value)) := by
  simp only [compileFuel, chooseInt]
  rw [ITree.bind_vis, demonicIfn_choose, ITree.bind_ret, demonicIfn_ret]

example : ProgramLogicCarte.runVoid 2 (demonicIfn (compileFuel 1 .pickInt)) =
    some (some (.lit (.int 0) : Value)) := by
  rw [show demonicIfn (compileFuel 1 .pickInt) =
    tau (ret (some (.lit (.int 0) : Value)) :
      ITree (VoidE : Type → Type 1) (Option Value)) by
    simp only [compileFuel, chooseInt]
    rw [ITree.bind_vis, demonicIfn_choose, ITree.bind_ret, demonicIfn_ret]]
  rw [ProgramLogicCarte.runVoid_tau, ProgramLogicCarte.runVoid_ret]

end ProgramLogicCarte.ExampleLang
