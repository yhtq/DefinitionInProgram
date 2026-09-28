import ITree.EffectAlgebra

/-! Recursive calls in interaction trees, corresponding to `callE` and `rec`. -/

namespace ITree

/-- A call of a recursive body with input `A`, returning a `B`. -/
inductive CallE (A B : Type) : Type → Type 1 where
  | call (input : A) : CallE A B B

def call {E : Type → Type 1} {A B : Type} (input : A) :
    ITree (CallE A B + E) B :=
  trigger (.inl (.call input))

/-- Execution state for interpreting recursive calls. The stack stores the
continuations suspended by calls. -/
abbrev RecState (E : Type → Type 1) (A B : Type) :=
  ITree (CallE A B + E) B × List (B → ITree (CallE A B + E) B)

/-- Interpret every recursive call by executing `body` with the requested
input. A call suspends its continuation until the body returns. -/
def recState (body : A → ITree (CallE A B + E) B)
    (initial : RecState E A B) : ITree E B :=
  .corecEmbed (fun (state : RecState E A B) =>
    let (tree, stack) := state
    match tree.dest with
    | ⟨.ret value, _⟩ =>
        match stack with
        | [] => .inl (ret value)
        | continuation :: rest =>
            .inr (tau' (.inr (continuation value, rest)))
    | ⟨.tau, child⟩ =>
        .inr (tau' (.inr (child 0, stack)))
    | ⟨.vis _ (.inl (.call next)), continuation⟩ =>
        .inr (tau' (.inr (body next, continuation :: stack)))
    | ⟨.vis _ (.inr event), continuation⟩ =>
        .inr (vis' event (fun answer => .inr (continuation answer, stack))))
    initial

def rec (body : A → ITree (CallE A B + E) B) (input : A) : ITree E B :=
  recState body (body input, [])

@[simp] theorem recState_ret_nil (body : A → ITree (CallE A B + E) B) (value : B) :
    recState body (ret value, []) = ret value := by
  conv => lhs; simp only [recState]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp] theorem recState_ret_cons (body : A → ITree (CallE A B + E) B)
    (value : B) (continuation : B → ITree (CallE A B + E) B)
    (stack : List (B → ITree (CallE A B + E) B)) :
    recState body (ret value, continuation :: stack) =
      tau (recState body (continuation value, stack)) := by
  conv => lhs; simp only [recState]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp] theorem recState_call (body : A → ITree (CallE A B + E) B)
    (next : A) (continuation : B → ITree (CallE A B + E) B)
    (stack : List (B → ITree (CallE A B + E) B)) :
    recState body (vis (SumE.inl (.call next)) continuation, stack) =
      tau (recState body (body next, continuation :: stack)) := by
  conv => lhs; simp only [recState]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp] theorem recState_vis (body : A → ITree (CallE A B + E) B)
    {α : Type} (event : E α) (continuation : α → ITree (CallE A B + E) B)
    (stack : List (B → ITree (CallE A B + E) B)) :
    recState body (vis (SumE.inr event) continuation, stack) =
      vis event (fun answer => recState body (continuation answer, stack)) := by
  conv => lhs; simp only [recState]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

/-- A body that immediately returns needs no recursive interpretation. -/
theorem rec_ret (body : A → ITree (CallE A B + E) B)
    (input : A) (value : B) (h : body input = ret value) :
    rec body input = ret value := by
  simpa only [rec, h] using recState_ret_nil body value

end ITree
