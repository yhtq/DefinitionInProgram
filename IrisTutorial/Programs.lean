import Iris.HeapLang.Lib.Par
import Iris.HeapLang.Lib.SpinLock

/-! Shared HeapLang programs from the POPL'21 Iris tutorial. -/

namespace IrisTutorial

open Iris BI ProgramLogic
open Iris.HeapLang

def swap : Val := hl_val(λ x y,
  let tmp := !x;
  x ← !y;
  y ← tmp)

def rotateRight : Val := hl_val(λ x y z,
  &swap y z;
  &swap x y)

def rotateLeft : Val := hl_val(λ x y z,
  &swap x y;
  &swap y z)

def sumList : Val := hl_val(rec sumList l :=
  match l with
  | none() => #0
  | some(p) =>
    let x := fst(!p);
    let l := snd(!p);
    x + sumList l)

def incList : Val := hl_val(rec incList n l :=
  match l with
  | none() => #()
  | some(p) =>
    let x := fst(!p);
    let l := snd(!p);
    p ← (n + x, l);
    incList n l)

def sumIncList : Val := hl_val(λ n l,
  &incList n l;
  &sumList l)

def mapList : Val := hl_val(rec mapList f l :=
  match l with
  | none() => #()
  | some(p) =>
    let x := fst(!p);
    let l := snd(!p);
    p ← (f x, l);
    mapList f l)

def parallelAdd : Exp := hl(
  let r := ref(#0);
  faa(r, #2) ‖ faa(r, #2);
  !r)

def parallelAddMul : Exp := hl(
  let r := ref(#0);
  let l := &HeapLang.SpinLock.newlock #();
  ((&HeapLang.SpinLock.acquire l; r ← !r + #2; &HeapLang.SpinLock.release l) ‖
   (&HeapLang.SpinLock.acquire l; r ← !r * #2; &HeapLang.SpinLock.release l));
  &HeapLang.SpinLock.acquire l;
  !r)

end IrisTutorial
