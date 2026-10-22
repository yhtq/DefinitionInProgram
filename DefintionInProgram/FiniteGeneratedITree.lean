import Iris.BI
import ITree.UpToTaus
import ProgramLogicCarte.Handler
import ProgramLogicCarte.Wpi
import ProgramLogicCarte.AngelicChoice
import ProgramLogicCarte.Step
import ProgramLogicCarte.State
import ProgramLogicCarte.StateOwnership
import ProgramLogicCarte.Void
import ProgramLogicCarte.UndefinedBehavior

open ProgramLogicCarte ITree Iris Iris.BI Iris.OFE ITree

namespace ITree
universe uε
variable {PROP : Type w} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]  {ε : Type v → Type uε}

def isIndexedF {ρ : Type v} {ι : Type*}
    (index_map : ι → (Π {α : Type v} {ρ : Type v}, α → ITree ε ρ))
    (k : DiscreteO (ITree ε ρ) → PROP)
    (t : DiscreteO (ITree ε ρ)) : PROP :=
  match t.car.dest with
  | ⟨.ret _, _⟩ => iprop(emp)
  | ⟨.tau, k'⟩ => iprop(|={∅}=> k ⟨k' 0⟩)
  | ⟨.vis _ _, k'⟩ =>
      -- let test := by
      --   dsimp only [P, children] at k'
      --   sorry
      -- sorry
      iprop(|={∅}=>
      ⌜∃ i : ι, k' = index_map i⌝
      ∗ ∀ a, k ⟨k' a⟩
      )

def isIndexed {ρ : Type v} {ι : Type*}
    (index_map : ι → (Π {α : Type v} {ρ : Type v}, α → ITree ε ρ))
    (t : ITree ε ρ) : PROP :=
  bi_greatest_fixpoint (isIndexedF index_map) ⟨t⟩

instance {ρ : Type v} {ι : Type*} {index_map : ι → (Π {α : Type v} {ρ : Type v}, α → ITree ε ρ)} : BIMonoPred (PROP := PROP) (isIndexedF (ρ := ρ) index_map) where
  mono_pred := by
    intros Phi Psi _ _
    iintro h %⟨x⟩
    apply dMatchOn x
    · intro _ h
      isimp [h, isIndexedF]
      iapply wand_rfl
    · intro x' h
      isimp [h, isIndexedF]
      iintro h'
      imod h'
      imodintro
      iapply h $$ h'
    · intro _ h x' hx
      isimp [hx, isIndexedF]
      iintro h'
      imod h'
      imodintro
      irevert h'
      iintro ⟨i, h''⟩
      iframe i
      iintro %_
      iapply h $$ h''
  mono_pred_ne := by
    intros Phi hPhi
    constructor
    intro n ⟨t1⟩ ⟨t2⟩ h
    obtain rfl := DiscreteO.dist_inj h
    rfl

/-- Coinduction establishes indexing without requiring termination. Visible
continuations must still belong to the same exact continuation map. -/
theorem isIndexed_coinduct {ρ : Type v} {ι : Type*}
    (index_map : ι → (Π {α : Type v} {ρ : Type v}, α → ITree ε ρ))
    (G : DiscreteO (ITree ε ρ) → PROP) [NonExpansive G] :
    ⊢ iprop(□ (∀ state, G state -∗ isIndexedF index_map G state) -∗
      ∀ t : ITree ε ρ, G ⟨t⟩ -∗ isIndexed index_map t) := by
  iintro #Hstep %t Ht
  unfold isIndexed
  iapply (greatest_fixpoint_coiter (F := isIndexedF index_map) G) $$ Hstep %⟨t⟩ Ht


@[simp]
theorem isIndexed_ret {ρ : Type v} {ι : Type*} {index_map : ι → (Π {α : Type v} {ρ : Type v}, α → ITree ε ρ)} {r : ρ} :
    ⊢ isIndexed (PROP := PROP) index_map (ret r) := by
  simp [isIndexed, greatest_fixpoint_unfold, isIndexedF]
  iempintro

@[simp]
theorem fin1Const_zero {α : Type*} (x : α) : fin1Const x 0 = x := rfl

@[simp]
theorem isIndexed_tau {ρ : Type v} {ι : Type*} {index_map : ι → (Π {α : Type v} {ρ : Type v}, α → ITree ε ρ)} {t : ITree ε ρ} :
    isIndexed (PROP := PROP) index_map (tau t) =
      iprop(|={∅}=> isIndexed (PROP := PROP) index_map t) := by
  conv_lhs =>
    rw [isIndexed, greatest_fixpoint_unfold]
    simp only [isIndexedF, dest_tau, fin1Const_zero]
  rfl

@[simp]
theorem isIndexed_vis {ρ : Type v} {ι : Type*} {index_map : ι → (Π {α : Type v} {ρ : Type v}, α → ITree ε ρ)} {e : ε α} {k : α → ITree ε ρ} :
    isIndexed (PROP := PROP) index_map (vis e k) =
      iprop(|={∅}=>
      ⌜∃ i : ι, k = index_map i⌝
      ∗ ∀ a, isIndexed (PROP := PROP) index_map (k a)
      ) := by
  conv_lhs =>
    rw [isIndexed, greatest_fixpoint_unfold]
    simp only [isIndexedF, dest_vis]
  rfl






/-- Finitely many exact visible continuations, with a coinductive certificate
for all branches. This is stronger than having finitely many code locations:
captured runtime data is part of continuation equality. -/
class FiniteIndex {ρ : Type v} (source : ITree ε ρ) where
  index : Type*
  [index_finite : Fintype index]
  start : index
  index_to_continuation : index → (Π {α : Type v} {ρ : Type v}, α → ITree ε ρ)
  is_indexed : ⊢ isIndexed (PROP := PROP) index_to_continuation source

attribute [instance_reducible] FiniteIndex.index_finite
attribute [instance] FiniteIndex.index_finite

/-- An unused total continuation supplies the polymorphic map for a return.
No visible node of a return needs to occur in this map. -/
private def unusedContinuation {α ρ : Type v} (_ : α) : ITree ε ρ :=
  .corecEmbed (fun _ : Unit => .inr (tau' (.inr ()))) ()

/-- With no visible effects left, every tree is coinductively indexed,
including trees with infinitely many silent steps. -/
theorem isIndexed_void {ρ : Type v} {ι : Type*}
    (index_map : ι → (Π {α : Type v} {ρ : Type v}, α → ITree VoidE ρ))
    (t : ITree VoidE ρ) : ⊢ isIndexed (PROP := PROP) index_map t := by
  ihave Hall : iprop(∀ tree : ITree VoidE ρ,
      emp -∗ isIndexed (PROP := PROP) index_map tree) $$ []
  · iapply (isIndexed_coinduct index_map (fun _ => iprop(emp)))
    iintro !> %⟨tree⟩ _
    apply dMatchOn tree
    · intro r htree
      subst tree
      isimp only [isIndexedF, dest_ret]
      iempintro
    · intro child htree
      subst tree
      isimp only [isIndexedF, dest_tau]
      imodintro
      iempintro
    · intro α event continuation htree
      cases event
  iapply Hall $$ %t
  iempintro

instance (priority := 80) finiteIndex_void {ρ : Type v} (t : ITree VoidE ρ) :
    FiniteIndex (PROP := PROP) t where
  index := ULift Unit
  index_finite := inferInstance
  start := .up ()
  index_to_continuation := fun _ => unusedContinuation
  is_indexed := isIndexed_void _ t

/-- Interpreting a state-only tree from a fixed initial state removes all
visible effects, so its result is finitely indexed without a termination
assumption. This does not cover residual choice or thread-pool events. -/
abbrev finiteIndex_stateIfn_void {S ρ : Type v} (initial : S)
    (t : ITree (StateE S + (VoidE : Type v → Type v)) ρ) :
    FiniteIndex (PROP := PROP) (stateIfn initial t) :=
  finiteIndex_void (PROP := PROP) (stateIfn initial t)

/-- Extend a typed continuation to the polymorphic interface of `FiniteIndex`.
The other type instances are unused and may return an arbitrary tree. -/
noncomputable def continuationMap {α ρ : Type v} (k : α → ITree ε ρ) :
    Π {β σ : Type v}, β → ITree ε σ := by
  classical
  intro β σ b
  exact if hβ : β = α then
    if hσ : σ = ρ then
      cast (congrArg (ITree ε) hσ.symm) (k (cast hβ b))
    else unusedContinuation b
  else unusedContinuation b

@[simp] theorem continuationMap_self {α ρ : Type v} (k : α → ITree ε ρ) :
    @continuationMap ε α ρ k α ρ = k := by
  funext a
  simp [continuationMap]

instance finiteIndex_ret {ρ : Type v} (r : ρ) :
    FiniteIndex (PROP := PROP) (ret r : ITree ε ρ) where
  index := ULift Unit
  index_finite := inferInstance
  start := .up ()
  index_to_continuation := fun _ => unusedContinuation
  is_indexed := isIndexed_ret

/-- A finite number of silent steps adds no visible continuation indices. -/
instance finiteIndex_tau {ρ : Type v} (t : ITree ε ρ)
    [h : FiniteIndex (PROP := PROP) t] : FiniteIndex (PROP := PROP) (tau t) where
  index := h.index
  index_finite := h.index_finite
  start := h.start
  index_to_continuation := h.index_to_continuation
  is_indexed := by
    rw [isIndexed_tau]
    iapply fupd_intro
    exact h.is_indexed

/-- An event followed by a return has exactly one continuation index, even
when the response type is infinite. -/
noncomputable instance finiteIndex_vis_ret {α ρ : Type v} (e : ε α) (f : α → ρ) :
    FiniteIndex (PROP := PROP) (vis e (fun a => ret (f a))) where
  index := ULift Unit
  index_finite := inferInstance
  start := .up ()
  index_to_continuation := fun _ => continuationMap (fun a => ret (f a))
  is_indexed := by
    rw [isIndexed_vis]
    imodintro
    isplit
    · ipureintro
      exact ⟨.up (), continuationMap_self _ |>.symm⟩
    · iintro %a
      exact isIndexed_ret

abbrev FiniteIndex.ofEq {ρ : Type v} {t t' : ITree ε ρ}
    (h : t = t') [FiniteIndex (PROP := PROP) t] : FiniteIndex (PROP := PROP) t' :=
  h ▸ inferInstance

end ITree
