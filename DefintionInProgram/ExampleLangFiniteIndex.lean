import DefintionInProgram.FiniteGeneratedITree
import ProgramLogicCarte.ExampleLang.Compile

/-!
# Exact finite indices for supported ExampleLang compilations

These results use the coinductive, exact-continuation definition.
They do not assert that every compiled expression satisfies it: runtime
values captured by subsequent visible continuations can give infinitely many
distinct continuation functions. Divergence itself is allowed.
-/

namespace ProgramLogicCarte.ExampleLang

open Iris Iris.BI ITree

variable {PROP : Type w} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]

abbrev finiteIndex_compileExpr_val (value : Value) :
    FiniteIndex (PROP := PROP) (compileExpr (.val value)) := by
  rw [compileExpr_val]
  infer_instance

abbrev finiteIndex_compileExpr_lam (binder : Binder) (body : Expr) :
    FiniteIndex (PROP := PROP) (compileExpr (.lam binder body)) := by
  rw [compileExpr_lam]
  infer_instance

abbrev finiteIndex_compileExpr_plus_values (left right : Int) :
    FiniteIndex (PROP := PROP)
      (compileExpr (.plus (.val (.lit (.int left))) (.val (.lit (.int right))))) := by
  rw [compileExpr_plus_values]
  infer_instance

abbrev finiteIndex_compileExpr_if_values (test : Int) (yes no : Value) :
    FiniteIndex (PROP := PROP)
      (compileExpr (.ite (.val (.lit (.int test))) (.val yes) (.val no))) := by
  rw [compileExpr_if_values]
  infer_instance

abbrev finiteIndex_compileExpr_beta (value : Value) :
    FiniteIndex (PROP := PROP)
      (compileExpr (.app (.val (.lam (.named "x") (.var "x"))) (.val value))) := by
  rw [compileExpr_beta]
  infer_instance

/-- Integer choice is infinite branching, but its single continuation does
not capture a value from a preceding event. It therefore has a finite index. -/
noncomputable abbrev finiteIndex_compileExpr_pickInt :
    FiniteIndex (PROP := PROP) (compileExpr .pickInt) := by
  rw [compileExpr_pickInt]
  infer_instance

/-- Any compilation with a finite silent-return certificate is indexed. -/
abbrev finiteIndex_compileExpr_of_tauN_ret (expr : Expr) (n : Nat) (value : Value)
    (h : compileExpr expr = tauN n (ret value)) :
    FiniteIndex (PROP := PROP) (compileExpr expr) := by
  rw [h]
  clear h
  induction n with
  | zero => exact finiteIndex_ret (PROP := PROP) value
  | succ n ih =>
      exact finiteIndex_tau (PROP := PROP) (h := ih) (tauN n (ret value))

end ProgramLogicCarte.ExampleLang
