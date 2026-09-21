/-!
# ExampleLang syntax

The syntax portion of upstream `examplelang/lang.v` is independent of the
heap and thread-pool back ends.  Keeping it in a separate module lets the
small examples exercise real source programs while those larger back ends are
translated incrementally.
-/

namespace ProgramLogicCarte.ExampleLang

inductive BaseLit where
  | int (value : Int)
  | loc (address : Nat)
deriving DecidableEq, Repr

inductive Binder where
  | anon
  | named (name : String)
deriving DecidableEq, Repr

mutual
  inductive Expr where
    | val (value : Value)
    | var (name : String)
    | lam (binder : Binder) (body : Expr)
    | app (fn arg : Expr)
    | plus (left right : Expr)
    | ite (test yes no : Expr)
    | ref (value : Expr)
    | load (address : Expr)
    | store (address value : Expr)
    | pickInt
    | spawn (body : Expr)
  deriving DecidableEq, Repr

  inductive Value where
    | lit (literal : BaseLit)
    | lam (binder : Binder) (body : Expr)
  deriving DecidableEq, Repr
end

def subst (name : String) (replacement : Value) : Expr → Expr
  | .val value => .val value
  | .var other => if name = other then .val replacement else .var other
  | .lam binder body =>
      match binder with
      | .anon => .lam binder (subst name replacement body)
      | .named bound =>
          if name = bound then .lam binder body else .lam binder (subst name replacement body)
  | .app fn arg => .app (subst name replacement fn) (subst name replacement arg)
  | .plus left right => .plus (subst name replacement left) (subst name replacement right)
  | .ite test yes no => Expr.ite (subst name replacement test) (subst name replacement yes)
      (subst name replacement no)
  | .ref value => .ref (subst name replacement value)
  | .load address => .load (subst name replacement address)
  | .store address value => .store (subst name replacement address) (subst name replacement value)
  | .pickInt => .pickInt
  | .spawn body => .spawn (subst name replacement body)

def substBinder (binder : Binder) (replacement : Value) : Expr → Expr
  | body => match binder with
    | .anon => body
    | .named name => subst name replacement body

def Value.toInt? : Value → Option Int
  | .lit (.int value) => some value
  | _ => none

def Value.toLam? : Value → Option (Binder × Expr)
  | .lam binder body => some (binder, body)
  | _ => none

@[simp]
theorem subst_same_var (name : String) (replacement : Value) :
    subst name replacement (.var name) = .val replacement := by
  simp [subst]

@[simp]
theorem subst_anon (_name : String) (replacement : Value) (body : Expr) :
    substBinder .anon replacement body = body :=
  rfl

@[simp]
theorem subst_named (name : String) (replacement : Value) (body : Expr) :
    substBinder (.named name) replacement body = subst name replacement body :=
  rfl

end ProgramLogicCarte.ExampleLang
