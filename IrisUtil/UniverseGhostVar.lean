import Iris.Instances.Lib.GhostVar

/-! Universe-polymorphic constant resource functors and ghost variables.
The upstream `constOF` and `GhostVarF` specialize their values to `Type 0`;
the underlying functor and proposition constructions are polymorphic. -/

namespace IrisUtil

open Iris COFE OFE ORA

universe u

abbrev constOF (B : Type u) : OFunctorPre.{u, u, u} := fun _ _ _ _ => B

instance [COFE B] : OFunctor (constOF B) where
  ofe := _
  map _ _ := ⟨id, id_ne⟩
  map_ne := by intros; constructor; simp
  map_id := by simp
  map_comp := by simp

instance [COFE B] : OFunctorContractive (constOF B) where
  map_contractive.1 := by simp [OFunctor.map]

instance [ORA B] : RFunctor (constOF B) where
  cmra := inferInstance
  map _ _ := (Hom.id : B -C> B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance [ORA B] [IncOrd B] : RFunctorAffine (constOF B) where
  affine := inferInstance

instance [ORA B] : RFunctorContractive (constOF B) where
  map_contractive.1 := fun _ => .rfl

abbrev GhostVarF (A : Type u) : OFunctorPre.{u, u, u} :=
  constOF (DFracAgree.DFracAgreeR (DiscreteO A))

class GhostVarG (GF : BundledGFunctors.{u, u, u}) (A : Type u) where
  [elemG : ElemG GF (GhostVarF A)]

attribute [reducible, instance] GhostVarG.elemG

variable {GF : BundledGFunctors.{u, u, u}} {A : Type u} [GhostVarG GF A]

def ghost_var_poly (γ : GName) (dq : DFrac) (a : A) : IProp GF :=
  iOwn (F := GhostVarF A) γ (DFracAgree.mk dq ⟨a⟩)

instance (γ : GName) (dq : DFrac) (a : A) : BI.Timeless (ghost_var_poly (GF := GF) γ dq a) := by
  unfold ghost_var_poly
  infer_instance

end IrisUtil
