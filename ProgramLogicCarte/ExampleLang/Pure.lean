import ProgramLogicCarte.ExampleLang.Syntax
import ProgramLogicCarte.Interpreter

/-!
# Executable pure fragment of ExampleLang

This is the closed, effect-free part of the source language from
`examplelang/lang.v`.  It deliberately leaves heap, concurrency, and
nondeterministic constructs to their corresponding effect handlers.  The
result is nevertheless an `ITree`, so it gives small end-to-end checks of the
source syntax, tree construction, and the `VoidE` interpreter.
-/

namespace ProgramLogicCarte.ExampleLang

open ITree

/-- Evaluate the arithmetic/conditional fragment of a closed expression. -/
def evalPure : Expr → Option Value
  | .val value => some value
  | .plus left right => do
      let leftValue ← evalPure left
      let rightValue ← evalPure right
      let leftInt ← leftValue.toInt?
      let rightInt ← rightValue.toInt?
      pure (.lit (.int (leftInt + rightInt)))
  | .ite test yes no => do
      let testValue ← evalPure test
      let testInt ← testValue.toInt?
      if testInt = 0 then evalPure no else evalPure yes
  | _ => none

/-- Compile the pure fragment to an effect-free interaction tree.  `none`
means that the expression belongs to one of the effectful fragments. -/
def compilePure (expr : Expr) : ITree (VoidE : Type → Type 1) (Option Value) :=
  ret (evalPure expr)

@[simp]
theorem run_compilePure (fuel : Nat) (expr : Expr) :
    ProgramLogicCarte.runVoid (VoidE := (VoidE : Type → Type 1)) (fuel + 1)
      (compilePure (VoidE := (VoidE : Type → Type 1)) expr) = some (evalPure expr) :=
  rfl

private def seven : Value := .lit (.int 7)
private def five : Value := .lit (.int 5)

example : evalPure (.plus (.val seven) (.val five)) = some (.lit (.int 12)) := by
  rfl

example : evalPure (.ite (.val (.lit (.int 0))) (.val seven) (.val five)) = some five := by
  rfl

example : evalPure (.ite (.val (.lit (.int 1))) (.val seven) (.val five)) = some seven := by
  rfl

example : evalPure (.app (.val seven) (.val five)) = none := by
  rfl

example : ProgramLogicCarte.runVoid (VoidE := (VoidE : Type → Type 1)) 1
    (compilePure (VoidE := (VoidE : Type → Type 1))
      (.plus (.val seven) (.val five))) = some (.some (.lit (.int 12))) := by
  rfl

end ProgramLogicCarte.ExampleLang
