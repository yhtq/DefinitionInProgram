import IrisTutorial.Programs

/-! Exercise 2: representation predicates for mutable linked lists. -/

namespace IrisTutorial.Exercise02

open Iris BI ProgramLogic
open Iris.HeapLang
open IrisTutorial

def isList {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]
    (xs : List Int) (v : Val) : IProp GF := iprop%
  match xs with
  | [] => ⌜v = hl_val(none())⌝
  | x :: xs => ∃ p : Loc, ⌜v = hl_val(some(#p))⌝ ∗
      ∃ v', p ↦ some hl_val((#x, &v')) ∗ isList xs v'

def listSum (xs : List Int) : Int := xs.foldr (· + ·) 0

end IrisTutorial.Exercise02
