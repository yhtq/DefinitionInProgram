import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.Vector3

/-! # ----------------------------------------------------------------------- -/
/-! # --------------------Start Vector3 Utilities---------------------------- -/
/-! # ----------------------------------------------------------------------- -/

instance {n : Nat} [Fin2.IsLT 0 n] : OfNat (ULift (Fin2 n)) 0 := ⟨.up <| .ofNat' 0⟩

instance {n : Nat} [Fin2.IsLT 1 n] : OfNat (ULift (Fin2 n)) 1 := ⟨.up <| .ofNat' 1⟩

def elim0 {α : Sort u} (i : ULift (Fin2 0)) : α :=
  i.down.elim0 (C := fun _ => α)

def fin1Const {α} (v : α) :=
  fun (i : ULift (Fin2 1)) =>
    match i.down with | .ofNat' 0 => v

open Vector3 in
def fin2Const {α} (x y : α) :=
  fun (i : ULift (Fin2 2)) => [x, y] i.down

theorem elim0_eq_all {α} : ∀ x : ULift (Fin2 0) → α, x = elim0 :=
  fun x => funext fun z => @z.down.elim0 fun _ => x z = elim0 z

theorem fin1Const_inj {α} {x y : α}
  (h : fin1Const x = fin1Const y) : x = y := by
  have := congr (a₁ := 0) h rfl
  simp only [fin1Const] at this
  exact this

theorem fin1Const_fin0 : fin1Const (c 0) = c := by
  funext i
  match i with
  | .up (.ofNat' 0) =>
    have fwd : Fin2 1 := i.down
    rfl

/-! # ----------------------------------------------------------------------- -/
/-! # --------------------End Vector3 Utilities------------------------------ -/
/-! # ----------------------------------------------------------------------- -/

/-! # ----------------------------------------------------------------------- -/
/-! # --------------------Start PFunctor Utilities--------------------------- -/
/-! # ----------------------------------------------------------------------- -/

theorem PFunctor.M.unfold_corec'_left.{uA, uB, u} {P : PFunctor.{uA, uB}} {α : Type u}
  (F : P.M ⊕ α → P (P.M ⊕ α))
  (h_eq : ∀ l, F (.inl l) = ⟨l.dest.1, Sum.inl ∘ l.dest.2⟩) :
  ∀ l, PFunctor.M.corec F (.inl l) = l := by
  intro l
  let R : P.M → P.M → Prop := fun t₁ t₂ => t₁ = PFunctor.M.corec F (.inl t₂)
  apply PFunctor.M.bisim R
  · intro t₁ t₂ h
    subst t₁
    rw [PFunctor.M.dest_corec, h_eq]
    rcases hdest : t₂.dest with ⟨a, g⟩
    exact ⟨a, _, g, rfl, rfl, fun _ => rfl⟩
  · exact rfl

def PFunctor.M.corecEmbed.{uA, uB, u} {P : PFunctor.{uA, uB}} {α : Type u}
    (F : α → P.M ⊕ P (P.M ⊕ α)) (x : α) : P.M :=
  let step : P.M ⊕ α → P (P.M ⊕ α) := fun s =>
    match s with
    | .inl l => P.map (@Sum.inl P.M α) l.dest
    | .inr r =>
      match F r with
      | .inl l => P.map (@Sum.inl P.M α) l.dest
      | .inr p => p
  PFunctor.M.corec step (.inr x)

theorem PFunctor.M.unfold_corecEmbed.{uA, uB, u} {P : PFunctor.{uA, uB}} {α : Type u}
  (F : α → P.M ⊕ P (P.M ⊕ α)) (x : α) :
  .corecEmbed F x =
  match F x with
  | .inl l => l
  | .inr ⟨a, g⟩ => .mk ⟨a, fun i ↦
    match g i with
    | .inl l => l
    | .inr r => .corecEmbed F r⟩ := by
  unfold corecEmbed
  generalize hFx : F x = fx
  cases fx with
  | inl l =>
    rw [PFunctor.M.corec_def]
    simp only
    rw [hFx]
    simp only [PFunctor.map]
    rw [← PFunctor.M.mk_dest l]
    rcases hdest : l.dest with ⟨a, g⟩
    congr
    funext i
    apply unfold_corec'_left
    intro l
    rfl
  | inr p =>
    rw [PFunctor.M.corec_def]
    simp only
    rw [hFx]
    rcases p with ⟨a, g⟩
    simp only [PFunctor.map]
    congr
    funext i
    split <;> rename_i hgi
    · simp only [Function.comp_apply]
      change PFunctor.M.corec _ (g i) = _
      rw [hgi]
      apply unfold_corec'_left
      intro l
      rfl
    · simp only [Function.comp_apply]
      change PFunctor.M.corec _ (g i) = _
      rw [hgi]

/-! # ----------------------------------------------------------------------- -/
/-! # --------------------End PFunctor Utilities--------------------------- -/
/-! # ----------------------------------------------------------------------- -/
