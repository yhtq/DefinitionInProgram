import IrisTutorial.Exercise02List

/-! Reference specifications and proof targets for tutorial unit 2.

The programs and predicates are direct HeapLang/Iris-Lean translations.  The
proofs deliberately remain visible as `sorry` targets while the Iris-Lean port
does not yet provide a translation of Coq's `iInduction` tactic. -/

namespace IrisTutorial.Solutions.Ex02SumList

open Iris BI ProgramLogic
open Iris.HeapLang
open IrisTutorial IrisTutorial.Exercise02

theorem sumList_spec_induction {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]
    (xs : List Int) (v : Val) :
    {{ isList (GF := GF) (hlc := hlc) xs v }} hl(&sumList &v)
    {{ RET hl_val(#(listSum xs)); isList (GF := GF) (hlc := hlc) xs v }} := by
  sorry

theorem incList_spec_induction {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]
    (n : Int) (xs : List Int) (v : Val) :
    {{ isList (GF := GF) (hlc := hlc) xs v }} hl(&incList #n &v)
    {{ RET hl_val(#()); isList (GF := GF) (hlc := hlc) (xs.map (n + ·)) v }} := by
  sorry

theorem sumIncList_spec {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]
    (n : Int) (xs : List Int) (v : Val) :
    {{ isList (GF := GF) (hlc := hlc) xs v }} hl(&sumIncList #n &v)
    {{ RET hl_val(#(listSum (xs.map (n + ·)))); isList (GF := GF) (hlc := hlc) (xs.map (n + ·)) v }} := by
  sorry

end IrisTutorial.Solutions.Ex02SumList
