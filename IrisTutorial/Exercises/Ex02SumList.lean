import IrisTutorial.Exercise02List

/-! Exercise skeletons for linked-list proofs. -/

namespace IrisTutorial.Exercises.Ex02SumList

open Iris BI ProgramLogic
open Iris.HeapLang
open IrisTutorial IrisTutorial.Exercise02

theorem incList_spec {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]
    (n : Int) (xs : List Int) (v : Val) :
    {{ isList (GF := GF) (hlc := hlc) xs v }} hl(&incList #n &v)
    {{ RET hl_val(#()); isList (GF := GF) (hlc := hlc) (xs.map (n + ·)) v }} := by
  sorry

end IrisTutorial.Exercises.Ex02SumList
