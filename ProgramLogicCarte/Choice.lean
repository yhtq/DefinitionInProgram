import ProgramLogicCarte.Wpi
import ProgramLogicCarte.Trace
import ITree.UpToTaus

/-! Demonic nondeterminism (`src/choice.v`). -/

namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE ITree

universe u w

/-- An event that lets the environment choose any inhabitant of `α`.
`Inhabited α` is retained from the Coq development so that a deterministic
interpreter can always select a branch. -/
inductive DemonicE : Type u → Type (u + 1) where
  | choose (α : Type u) (default : α) : DemonicE α

/-- Emit one demonic-choice event. -/
def demonicChoice (α : Type u) [Inhabited α] : ITree DemonicE α :=
  trigger (.choose α default)

/-- The logical handler for demonic choice requires every branch to satisfy
its continuation condition. -/
def demonicH {PROP : Type w} [BI PROP] : IHandlerBase PROP DemonicE where
  handle e Φ _ := match e with
    | .choose _ _ => iprop(∀ x, Φ x)
  mono e := by
    cases e
    intro Φ Φ' spawned spawned'
    istart
    iintro HΦ _ HAll
    iintro %x
    ispecialize HΦ $$ %x
    ispecialize HAll $$ %x
    iapply HΦ
    iexact HAll
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    cases e
    exact forall_ne hΦ

instance demonicHSequential {PROP : Type w} [BI PROP] :
    IHandler.Sequential (demonicH : IHandlerBase PROP DemonicE) where
  sequential e Φ spawned := by
    cases e
    exact .rfl

/-- WP rule for a demonic choice handled directly by `demonicH`. -/
theorem wpi_demonicChoice {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    (α : Type u) [Inhabited α] (Φ : α → PROP) :
    iprop(∀ x, Φ x) ⊢ wpi demonicH (demonicChoice α) Φ := by
  rw [demonicChoice, trigger, wpi_vis]
  istart
  iintro HAll
  imodintro
  isimp only [demonicH]
  iintro %x
  rw [wpi_ret]
  imodintro
  ispecialize HAll $$ %x
  iexact HAll

/-- Demonic choice is valid under any invariant mask. -/
theorem wpiMask_demonicChoice {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    (mask : CoPset) (α : Type u) [Inhabited α] (Φ : α → PROP) :
    iprop(∀ x, Φ x) ⊢ wpiMask demonicH mask (demonicChoice α) Φ := by
  rw [wpiMask]
  istart
  iintro HAll
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  rw [demonicChoice, trigger, wpi_vis]
  imodintro
  isimp only [demonicH]
  iintro %x
  rw [wpi_ret]
  imodintro
  iapply (fupd_wand_left (P := (emp : PROP)))
  isplitl [HAll]
  · iintro _
    ispecialize HAll $$ %x
    iexact HAll
  · iexact Hclose

/-- One-layer unfolding relation for a concrete resolution of demonic
choices. A demonic event chooses one branch and takes a silent step. -/
inductive DemonicIrelF {ε : Type u → Type (u + 1)} {ρ : Type*}
    (sim : ITree (DemonicE + ε) ρ → ITree ε ρ → Prop) :
    ITree (DemonicE + ε) ρ → ITree ε ρ → Prop where
  | choose (α : Type u) (default x : α)
      (k : α → ITree (DemonicE + ε) ρ) (t : ITree ε ρ)
      (h : sim (k x) t) :
      DemonicIrelF sim (vis (SumE.inl (.choose α default)) k) (tau t)
  | ret (x : ρ) : DemonicIrelF sim (ret x) (ret x)
  | tau (t : ITree (DemonicE + ε) ρ) (t' : ITree ε ρ) (h : sim t t') :
      DemonicIrelF sim (tau t) (tau t')
  | vis {α : Type u} (e : ε α)
      (k : α → ITree (DemonicE + ε) ρ) (k' : α → ITree ε ρ)
      (h : ∀ x, sim (k x) (k' x)) :
      DemonicIrelF sim (vis (SumE.inr e) k) (vis e k')

theorem DemonicIrelF_monotone {ε : Type u → Type (u + 1)} {ρ : Type*}
    {sim sim' : ITree (DemonicE + ε) ρ → ITree ε ρ → Prop}
    (hmono : ∀ t t', sim t t' → sim' t t') :
    ∀ {t t'}, DemonicIrelF sim t t' → DemonicIrelF sim' t t' := by
  intro t t' h
  cases h with
  | choose α default x k t h => exact .choose α default x k t (hmono _ _ h)
  | ret x => exact .ret x
  | tau t t' h => exact .tau t t' (hmono _ _ h)
  | vis e k k' h => exact .vis e k k' (fun x => hmono _ _ (h x))

def DemonicIrelOp {ε : Type u → Type (u + 1)} {ρ : Type*}
    (sim : ITree (DemonicE + ε) ρ → ITree ε ρ →
      Lean.Order.ReverseImplicationOrder) :
    ITree (DemonicE + ε) ρ → ITree ε ρ →
      Lean.Order.ReverseImplicationOrder :=
  fun t t' => DemonicIrelF sim t t'

theorem DemonicIrelOp_monotone {ε : Type u → Type (u + 1)} {ρ : Type*} :
    Lean.Order.monotone (@DemonicIrelOp ε ρ) := by
  intro sim sim' hsim t t' h
  exact DemonicIrelF_monotone (fun a b => hsim a b) h

/-- A concrete tree resolves every demonic event of the source tree. -/
noncomputable def DemonicIrel {ε : Type u → Type (u + 1)} {ρ : Type*}
    (t : ITree (DemonicE + ε) ρ) (t' : ITree ε ρ) : Prop :=
  ITree.reverseToProp
    (Lean.Order.lfp_monotone (@DemonicIrelOp ε ρ)
      DemonicIrelOp_monotone t t')

theorem DemonicIrel_unfold {ε : Type u → Type (u + 1)} {ρ : Type*}
    (t : ITree (DemonicE + ε) ρ) (t' : ITree ε ρ) :
    DemonicIrel t t' ↔ DemonicIrelF DemonicIrel t t' := by
  unfold DemonicIrel ITree.reverseToProp
  delta Lean.Order.lfp_monotone
  conv_lhs => rw [Lean.Order.lfp_fix DemonicIrelOp_monotone]
  rfl

theorem DemonicIrel_coinduct {ε : Type u → Type (u + 1)} {ρ : Type*}
    (R : ITree (DemonicE + ε) ρ → ITree ε ρ → Prop)
    (hstep : ∀ t t', R t t' → DemonicIrelF R t t') :
    ∀ t t', R t t' → DemonicIrel t t' := by
  have hpost : Lean.Order.PartialOrder.rel
      (@DemonicIrelOp ε ρ
        (fun t t' => (R t t' : Lean.Order.ReverseImplicationOrder)))
      (fun t t' => (R t t' : Lean.Order.ReverseImplicationOrder)) := by
    change ∀ t t', R t t' → DemonicIrelF R t t'
    exact hstep
  have hlfp := Lean.Order.lfp_le_of_le hpost
  intro t t' h
  unfold DemonicIrel ITree.reverseToProp
  exact hlfp t t' h

/-- The relation respects strong tree bisimulation. In this Lean encoding,
strong bisimulation coincides with equality of `ITree`s. -/
theorem DemonicIrel_congr {ε : Type u → Type (u + 1)} {ρ : Type*}
    {t₁ t₂ : ITree (DemonicE + ε) ρ} {u₁ u₂ : ITree ε ρ}
    (ht : IEq t₁ t₂) (hu : IEq u₁ u₂) :
    DemonicIrel t₁ u₁ ↔ DemonicIrel t₂ u₂ := by
  rw [ieq_iff_eq] at ht hu
  subst t₂
  subst u₂
  rfl

/-- Resolve every demonic choice using the default value stored in its event. -/
def demonicIfn {ε : Type u → Type (u + 1)} {ρ : Type*}
    (t : ITree (DemonicE + ε) ρ) : ITree ε ρ :=
  .corecEmbed (fun t =>
    match t.dest with
    | ⟨.ret x, _⟩ => .inl (ret x)
    | ⟨.tau, c⟩ => .inr (tau' (.inr (c 0)))
    | ⟨.vis α (.inl e), k⟩ =>
        match e with
        | .choose _ default => .inr (tau' (.inr (k default)))
    | ⟨.vis _ (.inr e), k⟩ => .inr (vis' e (fun x => .inr (k x)))) t

@[simp]
theorem demonicIfn_ret {ε : Type u → Type (u + 1)} {ρ : Type*} (x : ρ) :
    demonicIfn (ε := ε) (ret x) = ret x := by
  conv => lhs; simp only [demonicIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem demonicIfn_tau {ε : Type u → Type (u + 1)} {ρ : Type*}
    (t : ITree (DemonicE + ε) ρ) :
    demonicIfn (tau t) = tau (demonicIfn t) := by
  conv => lhs; simp only [demonicIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem demonicIfn_choose {ε : Type u → Type (u + 1)} {ρ : Type*}
    {α : Type u} (default : α) (k : α → ITree (DemonicE + ε) ρ) :
    demonicIfn (vis (SumE.inl (.choose α default)) k) =
      tau (demonicIfn (k default)) := by
  conv => lhs; simp only [demonicIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp]
theorem demonicIfn_vis {ε : Type u → Type (u + 1)} {ρ : Type*}
    {α : Type u} (e : ε α) (k : α → ITree (DemonicE + ε) ρ) :
    demonicIfn (vis (SumE.inr e) k) = vis e (fun x => demonicIfn (k x)) := by
  conv => lhs; simp only [demonicIfn]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

theorem demonicIfn_irel {ε : Type u → Type (u + 1)} {ρ : Type*}
    (t : ITree (DemonicE + ε) ρ) : DemonicIrel t (demonicIfn t) := by
  apply DemonicIrel_coinduct (fun s t' => t' = demonicIfn s)
  · intro s t' h
    subst t'
    apply s.dMatchOn
    · intro x hx
      rw [hx, demonicIfn_ret]
      exact .ret x
    · intro next hnext
      rw [hnext, demonicIfn_tau]
      exact .tau next _ rfl
    · intro α e k hk
      rw [hk]
      cases e with
      | inl choice =>
          cases choice with
          | choose default =>
              rw [demonicIfn_choose]
              exact .choose α default default k _ rfl
      | inr e =>
          rw [demonicIfn_vis]
          exact .vis e k _ (fun _ => rfl)
  · exact rfl

/-- For every concrete resolution of a source tree, its target WP holds. -/
private def demonicAdequacyPred {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type (u + 1)} {ρ : Type*} (H : IHandlerBase PROP ε)
    (state : WpiState PROP (DemonicE + ε) ρ) : PROP :=
  iprop(∀ t' : ITree ε ρ,
    ∀ _ : DemonicIrel state.1.car t', wpi H t' state.2)

private instance demonicAdequacyPred_ne {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type (u + 1)} {ρ : Type*} (H : IHandlerBase PROP ε) :
    NonExpansive (demonicAdequacyPred (ρ := ρ) H) where
  ne := by
    intro n state₁ state₂ hstate
    rcases state₁ with ⟨⟨t₁⟩, Φ₁⟩
    rcases state₂ with ⟨⟨t₂⟩, Φ₂⟩
    rcases hstate with ⟨ht, hΦ⟩
    obtain rfl := DiscreteO.dist_inj ht
    unfold demonicAdequacyPred
    exact forall_ne fun t' => forall_ne fun _ =>
      NonExpansive.ne (f := wpi H t') hΦ

/-- Demonic relational interpretation preserves the empty-mask weakest
precondition. This is the fixed-point induction step for masked adequacy. -/
theorem demonic_adequacy_empty {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type (u + 1)} {ρ : Type*} (H : IHandlerBase PROP ε)
    (t : ITree (DemonicE + ε) ρ) (t' : ITree ε ρ) (Φ : ρ → PROP)
    (hrel : DemonicIrel t t') :
    wpi (demonicH ⊕ₕ H) t Φ ⊢ wpi H t' Φ := by
  iintro Hwp
  ihave Hgen : iprop(∀ state : WpiState PROP (DemonicE + ε) ρ,
      wpi (demonicH ⊕ₕ H) state.1.car state.2 -∗
        demonicAdequacyPred H state) $$ []
  · iapply (wpi_iter (demonicH ⊕ₕ H) (demonicAdequacyPred (ρ := ρ) H))
    iintro !> %state HF
    rcases state with ⟨⟨tree⟩, post⟩
    apply tree.dMatchOn
    · intro value htree
      subst tree
      isimp only [wpiF', wpiF, dest_ret] at HF
      isimp only [demonicAdequacyPred]
      iintro %target %hrel
      have hstep := (DemonicIrel_unfold (ret value) target).mp hrel
      generalize hsource : (ret value : ITree (DemonicE + ε) ρ) = source at hstep
      cases hstep with
      | ret x =>
          have hv : value = x := ITree.ret_inj hsource
          subst x
          rw [wpi_ret]
          iexact HF
      | choose α default x k t h =>
          have hshape := congrArg (fun t => t.dest.fst) hsource
          simp only [dest_ret, dest_vis] at hshape
          cases hshape
      | tau next next' h =>
          have hshape := congrArg (fun t => t.dest.fst) hsource
          simp only [dest_ret, dest_tau] at hshape
          cases hshape
      | vis e k k' h =>
          have hshape := congrArg (fun t => t.dest.fst) hsource
          simp only [dest_ret, dest_vis] at hshape
          cases hshape
    · intro child htree
      subst tree
      isimp only [wpiF', wpiF, dest_tau] at HF
      isimp only [demonicAdequacyPred]
      iintro %target %hrel
      have hstep := (DemonicIrel_unfold (tau child) target).mp hrel
      generalize hsource : (tau child : ITree (DemonicE + ε) ρ) = source at hstep
      cases hstep with
      | tau next next' h =>
          have hn : child = next := ITree.tau_inj hsource
          subst next
          rw [wpi_tau_step]
          imod HF with HF
          imodintro
          isimp only [demonicAdequacyPred] at HF
          ispecialize HF $$ %next'
          ispecialize HF $$ %h
          iexact HF
      | choose α default x k t h =>
          have hshape := congrArg (fun t => t.dest.fst) hsource
          simp only [dest_tau, dest_vis] at hshape
          cases hshape
      | ret x =>
          have hshape := congrArg (fun t => t.dest.fst) hsource
          simp only [dest_tau, dest_ret] at hshape
          cases hshape
      | vis e k k' h =>
          have hshape := congrArg (fun t => t.dest.fst) hsource
          simp only [dest_tau, dest_vis] at hshape
          cases hshape
    · intro α event continuation htree
      subst tree
      isimp only [wpiF', wpiF, dest_vis] at HF
      isimp only [demonicAdequacyPred]
      iintro %target %hrel
      have hstep := (DemonicIrel_unfold (vis event continuation) target).mp hrel
      generalize hsource : (vis event continuation : ITree (DemonicE + ε) ρ) = source at hstep
      cases event with
      | inl choice =>
          cases choice with
          | choose default =>
              cases hstep with
              | choose β other x k resolved h =>
                  have hα : α = β := ITree.vis_inj_α hsource
                  subst β
                  have hparts := ITree.vis_inj hsource
                  have hk : continuation = k := hparts.2
                  subst k
                  rw [wpi_tau_step]
                  imod HF with HF
                  imodintro
                  isimp only [IHandler.sum, demonicH] at HF
                  ispecialize HF $$ %x
                  isimp only [demonicAdequacyPred] at HF
                  ispecialize HF $$ %resolved
                  ispecialize HF $$ %h
                  iexact HF
              | ret x =>
                  have hshape := congrArg (fun t => t.dest.fst) hsource
                  simp only [dest_vis, dest_ret] at hshape
                  cases hshape
              | tau next next' h =>
                  have hshape := congrArg (fun t => t.dest.fst) hsource
                  simp only [dest_vis, dest_tau] at hshape
                  cases hshape
              | vis e k k' h =>
                  have hshape := congrArg (fun t => t.dest.fst) hsource
                  simp only [dest_vis] at hshape
                  cases hshape
      | inr e =>
          cases hstep with
          | vis e' k k' h =>
              have hα : α = _ := ITree.vis_inj_α hsource
              cases hα
              have hparts := ITree.vis_inj hsource
              have he : e = e' := by cases hparts.1; rfl
              have hk : continuation = k := hparts.2
              subst e'
              subst k
              rw [wpi_vis]
              imod HF with HF
              imodintro
              isimp only [IHandler.sum] at HF
              iapply (H.mono e
                (fun a => demonicAdequacyPred H (⟨⟨continuation a⟩, post⟩))
                (fun a => wpi H (k' a) post)
                (fun a => fupd ⊤ ∅ (demonicAdequacyPred H
                  (⟨⟨continuation a⟩, fun _ => iprop(False)⟩)))
                (fun a => fupd ⊤ ∅ (wpi H (k' a) (fun _ => iprop(False))))) $$ [] [] HF
              · iintro %a Ha
                isimp only [demonicAdequacyPred] at Ha
                ispecialize Ha $$ %(k' a)
                ispecialize Ha $$ %(h a)
                iexact Ha
              · iintro !> %a Ha
                imod Ha with Ha
                imodintro
                isimp only [demonicAdequacyPred] at Ha
                ispecialize Ha $$ %(k' a)
                ispecialize Ha $$ %(h a)
                iexact Ha
          | choose β default x k resolved h =>
              have hshape := congrArg (fun t => t.dest.fst) hsource
              simp only [dest_vis] at hshape
              cases hshape
          | ret x =>
              have hshape := congrArg (fun t => t.dest.fst) hsource
              simp only [dest_vis, dest_ret] at hshape
              cases hshape
          | tau next next' h =>
              have hshape := congrArg (fun t => t.dest.fst) hsource
              simp only [dest_vis, dest_tau] at hshape
              cases hshape
  ispecialize Hgen $$ %(⟨⟨t⟩, Φ⟩)
  ispecialize Hgen $$ Hwp
  isimp only [demonicAdequacyPred] at Hgen
  ispecialize Hgen $$ %t'
  ispecialize Hgen $$ %hrel
  iexact Hgen

/-- Demonic relational interpretation preserves WP under any invariant mask. -/
theorem demonic_adequacy {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type (u + 1)} {ρ : Type*} (H : IHandlerBase PROP ε)
    (mask : CoPset) (t : ITree (DemonicE + ε) ρ)
    (t' : ITree ε ρ) (Φ : ρ → PROP) (hrel : DemonicIrel t t') :
    wpiMask (demonicH ⊕ₕ H) mask t Φ ⊢ wpiMask H mask t' Φ := by
  unfold wpiMask
  exact fupd_mono (demonic_adequacy_empty H t t'
    (fun result => iprop(|={∅, mask}=> Φ result)) hrel)

/-- Every finite source trace has a concrete resolution with its demonic
events erased from the visible trace. -/
theorem demonic_trace {ε : Type u → Type (u + 1)} {ρ : Type*}
    {tr : Trace (DemonicE + ε) ρ} {t : ITree (DemonicE + ε) ρ}
    (htr : Trace.IsTrace tr t) :
    ∃ t' : ITree ε ρ, DemonicIrel t t' ∧
      Trace.IsTrace (Trace.eraseLeft tr) t' := by
  classical
  induction htr with
  | ret x =>
      exact ⟨ret x, (DemonicIrel_unfold _ _).mpr (.ret x), .ret x⟩
  | vis e answer k tr h ih =>
      obtain ⟨t', hrel, htrace⟩ := ih
      cases e with
      | inl choice =>
          cases choice with
          | choose default =>
              exact ⟨tau t', (DemonicIrel_unfold _ _).mpr
                (.choose _ default answer k t' hrel), .tau htrace⟩
      | inr e =>
          let k' : _ → ITree ε ρ :=
            fun x => if x = answer then t' else demonicIfn (k x)
          refine ⟨vis e k', (DemonicIrel_unfold _ _).mpr (.vis e k k' ?_), ?_⟩
          · intro x
            by_cases hx : x = answer
            · subst x
              simpa [k'] using hrel
            · simpa [k', hx] using demonicIfn_irel (k x)
          · exact .vis e answer k' _ (by simpa [k'] using htrace)
  | visEmpty e k empty =>
      cases e with
      | inl choice =>
          cases choice with
          | choose default => exact False.elim (empty default)
      | inr e =>
          let k' : _ → ITree ε ρ := fun x => False.elim (empty x)
          refine ⟨vis e k', (DemonicIrel_unfold _ _).mpr (.vis e k k' ?_), ?_⟩
          · intro x
            exact False.elim (empty x)
          · exact .visEmpty e k' empty
  | cut t =>
      exact ⟨demonicIfn t, demonicIfn_irel t, .cut _⟩
  | tau h ih =>
      obtain ⟨t', hrel, htrace⟩ := ih
      exact ⟨tau t', (DemonicIrel_unfold _ _).mpr (.tau _ _ hrel), .tau htrace⟩

/-- A source trace can be resolved to an execution whose masked WP follows
from the source WP. -/
theorem demonic_trace_adequacy {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ε : Type u → Type (u + 1)} {ρ : Type*} (H : IHandlerBase PROP ε)
    (mask : CoPset) {tr : Trace (DemonicE + ε) ρ}
    {t : ITree (DemonicE + ε) ρ} (Φ : ρ → PROP)
    (htr : Trace.IsTrace tr t) :
    ∃ t' : ITree ε ρ,
      Trace.IsTrace (Trace.eraseLeft tr) t' ∧
      (wpiMask (demonicH ⊕ₕ H) mask t Φ ⊢ wpiMask H mask t' Φ) := by
  obtain ⟨t', hrel, htrace⟩ := demonic_trace htr
  exact ⟨t', htrace, demonic_adequacy H mask t t' Φ hrel⟩


end ProgramLogicCarte
