import ProgramLogicCarte.Wpi
import ITree.UpToTaus
import ITree.Translate

/-! Breakpoint markers and weakest preconditions up to the next marker. -/

namespace ProgramLogic

open Iris Iris.BI ITree ProgramLogicCarte

universe u v uρ w

/-- A marker carrying a label and a unique unit response. -/
inductive BreakpointE (ι : Type u) : Type u → Type (max u v) where
  | bp (i : ι) : BreakpointE ι (ULift Unit)

def breakpoint {ι : Type*} (i : ι) : ITree (BreakpointE ι) (ULift Unit) :=
  trigger (BreakpointE.bp i)

def breakpointH {PROP : Type w} [BI PROP] {ι : Type*} : IHandlerBase PROP (BreakpointE ι) where
  handle e Φ _ := match e with
    | .bp i => iprop(Φ (.up ()))
  mono e := by
    cases e
    intro Φ Φ' spawned spawned'
    istart
    iintro HΦ _ H
    iapply HΦ $$ H
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    cases e
    exact hΦ (.up ())

theorem wpi_breakpoint {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ι : Type*} (i : ι) (Φ : ULift Unit → PROP) :
    Φ (.up ()) ⊢ wpi breakpointH (breakpoint i) Φ := by
  simp only [breakpointH, breakpoint, trigger, wpi_vis, wpi_ret]
  istart
  iintro h
  imodintro
  imodintro
  iexact h

private abbrev bp_extraction (e : BreakpointE ι α) : α :=
  match e with
  | .bp i => .up ()

def breakpointInter {ι : Type u} {ε : Type u → Type (max u v)} {ρ : Type uρ}
    (t : ITree (BreakpointE ι + ε) ρ) : ITree ε ρ :=
  .corecEmbed (fun tree =>
    match tree.dest with
    | ⟨.ret r, _⟩ => .inl (ret r)
    | ⟨.tau, k⟩ => .inr (tau' (.inr (k 0)))
    | ⟨.vis _ (.inl (.bp _)), k⟩ => .inr <| tau' <| .inr (k (.up ()))
    | ⟨.vis _ (.inr e), k⟩ => .inr (vis' e (fun a => .inr (k a)))) t


 -- ITree.dMatchOn t (fun v _ => .ret v) (fun c _ => .tau (breakpointInter c))
  --   (fun α e k hx => match e with
  --     | .inl e => breakpointInter <| k (bp_extraction e)
  --     | .inr e => vis e (breakpointInter ∘ k)
  --   )

/-- The end of a segment: either execution returned before a breakpoint, or
it reached a marker. At a marker, `rest` is the suspended tree after the
marker; no execution of `rest` is required. -/
inductive BreakpointResult (ι : Type u) (ε : Type u → Type (max u v)) (ρ : Type uρ) where
  | returned (value : ρ)
  | stopped (label : ι) (rest : ITree (BreakpointE ι + ε) ρ)

/-- Keep the events before the first breakpoint and turn that breakpoint
into a return carrying its label and suspended continuation. Ordinary events
and silent steps retain their order. -/
def untilBreakpoint {ι : Type u} {ε : Type u → Type (max u v)} {ρ : Type uρ}
    (t : ITree (BreakpointE ι + ε) ρ) : ITree ε (BreakpointResult ι ε ρ) :=
  .corecEmbed (fun tree =>
    match tree.dest with
    | ⟨.ret r, _⟩ => .inl (ret (.returned r))
    | ⟨.tau, k⟩ => .inr (tau' (.inr (k 0)))
    | ⟨.vis _ (.inl (.bp label)), k⟩ => .inl (ret (.stopped label (k (.up ()))))
    | ⟨.vis _ (.inr e), k⟩ => .inr (vis' e (fun a => .inr (k a)))) t

@[simp] theorem untilBreakpoint_ret {ι : Type u} {ε : Type u → Type (max u v)} {ρ : Type uρ}
    (r : ρ) :
    untilBreakpoint (ret r : ITree (BreakpointE ι + ε) ρ) = ret (.returned r) := by
  conv_lhs => simp only [untilBreakpoint]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp] theorem untilBreakpoint_tau {ι : Type u} {ε : Type u → Type (max u v)} {ρ : Type uρ}
    (t : ITree (BreakpointE ι + ε) ρ) :
    untilBreakpoint (tau t) = tau (untilBreakpoint t) := by
  conv_lhs => simp only [untilBreakpoint]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp] theorem untilBreakpoint_bp {ι : Type u} {ε : Type u → Type (max u v)} {ρ : Type uρ}
    (label : ι) (k : ULift Unit → ITree (BreakpointE ι + ε) ρ) :
    untilBreakpoint (vis (.inl (.bp label)) k) = ret (.stopped label (k (.up ()))) := by
  conv_lhs => simp only [untilBreakpoint]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

@[simp] theorem untilBreakpoint_vis {ι : Type u} {ε : Type u → Type (max u v)} {ρ : Type uρ}
    {α : Type u} (e : ε α) (k : α → ITree (BreakpointE ι + ε) ρ) :
    untilBreakpoint (vis (.inr e) k) = vis e (fun a => untilBreakpoint (k a)) := by
  conv_lhs => simp only [untilBreakpoint]; rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

variable {PROP : Type w} [BI PROP] [BIFUpdate PROP]
    {ι : Type u} {ε : Type u → Type (max u v)} {ρ : Type uρ} (H : IHandlerBase PROP ε)

/-- Weakest precondition up to the first breakpoint, using `H` for ordinary
events. The postcondition describes a `returned` or `stopped` result. It can
require `False` for `returned` to insist that a breakpoint is reached.

As in `wpi`, the least fixed point requires reaching the segment endpoint;
divergence before the first breakpoint is not accepted. Spawned branches use
the same false postcondition as ordinary `wpi`. -/
def wpiUntil
    (t : ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) : PROP :=
  wpi H (untilBreakpoint t) Φ

/-- Run up to the first breakpoint with the invariant mask opened for the
segment and restored at its endpoint. -/
def wpiUntilMask
    (mask : CoPset) (t : ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) : PROP :=
  wpiMask H mask (untilBreakpoint t) Φ

instance wpiUntilMask_ne
    (mask : CoPset) (t : ITree (BreakpointE ι + ε) ρ) :
    Iris.OFE.NonExpansive (wpiUntilMask H mask t) where
  ne := by
    intro n Φ₁ Φ₂ hΦ
    unfold wpiUntilMask wpiMask
    apply BIFUpdate.ne.ne
    apply Iris.OFE.NonExpansive.ne (f := wpi H (untilBreakpoint t))
    intro result
    exact BIFUpdate.ne.ne (hΦ result)

instance wpiUntil_ne
    (t : ITree (BreakpointE ι + ε) ρ) :
    Iris.OFE.NonExpansive (wpiUntil H t) :=
  wpi_ne H (untilBreakpoint t)

@[simp] theorem wpiUntil_ret
    (r : ρ) (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntil H (ret r) Φ = iprop(|={∅}=> Φ (.returned r)) := by
  rw [wpiUntil, untilBreakpoint_ret, wpi_ret]

@[simp] theorem wpiUntil_tau_step
    (t : ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntil H (tau t) Φ = iprop(|={∅}=> wpiUntil H t Φ) := by
  rw [wpiUntil, untilBreakpoint_tau, wpi_tau_step]
  rfl

theorem wpiUntil_tau
    (t : ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntil H (tau t) Φ = wpiUntil H t Φ := by
  unfold wpiUntil
  rw [untilBreakpoint_tau, ← wpi_tau]

/-- Stop at the marker: the continuation is passed to the postcondition,
and its weakest precondition is not calculated. -/
@[simp] theorem wpiUntil_bp
    (label : ι)
    (k : ULift Unit → ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntil H (vis (.inl (.bp label)) k) Φ =
      iprop(|={∅}=> Φ (.stopped label (k (.up ())))) := by
  rw [wpiUntil, untilBreakpoint_bp, wpi_ret]

@[simp] theorem wpiUntil_vis
    {α : Type u} (e : ε α)
    (k : α → ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntil H (vis (.inr e) k) Φ = iprop(|={∅}=> H.handle e
      (fun a => wpiUntil H (k a) Φ)
      (fun a => fupd ⊤ ∅ (wpiUntil H (k a) (fun _ => iprop(False))))) := by
  rw [wpiUntil, untilBreakpoint_vis, wpi_vis]
  rfl

/-- Unfold the masked WP at a return. -/
@[simp] theorem wpiUntilMask_ret
    (mask : CoPset) (r : ρ) (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntilMask H mask (ret r) Φ =
      iprop(|={mask, ∅}=> |={∅}=> |={∅, mask}=> Φ (.returned r)) := by
  simp only [wpiUntilMask, wpiMask, untilBreakpoint_ret, wpi_ret]

/-- A return needs only its postcondition, even with a nonempty mask. -/
theorem wpiUntilMask_ret_intro
    (mask : CoPset) (r : ρ) (Φ : BreakpointResult ι ε ρ → PROP) :
    Φ (.returned r) ⊢ wpiUntilMask H mask (ret r) Φ := by
  simpa only [wpiUntilMask, untilBreakpoint_ret] using
    (wpiMask_ret H mask (.returned r) Φ)

@[simp] theorem wpiUntilMask_tau_step
    (mask : CoPset) (t : ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntilMask H mask (tau t) Φ =
      iprop(|={mask, ∅}=> |={∅}=> wpiUntil H t
        (fun result => iprop(|={∅, mask}=> Φ result))) := by
  simp only [wpiUntilMask, wpiMask, untilBreakpoint_tau, wpi_tau_step, wpiUntil]

@[simp] theorem wpiUntilMask_tau
    (mask : CoPset) (t : ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntilMask H mask (tau t) Φ = wpiUntilMask H mask t Φ := by
  simp only [wpiUntilMask, wpiMask, untilBreakpoint_tau, ← wpi_tau]

/-- The suspended continuation is not checked after reaching a marker. -/
@[simp] theorem wpiUntilMask_bp
    (mask : CoPset) (label : ι)
    (k : ULift Unit → ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntilMask H mask (vis (.inl (.bp label)) k) Φ =
      iprop(|={mask, ∅}=> |={∅}=> |={∅, mask}=>
        Φ (.stopped label (k (.up ())))) := by
  simp only [wpiUntilMask, wpiMask, untilBreakpoint_bp, wpi_ret]

/-- At a marker, only the postcondition for its suspended continuation is needed. -/
theorem wpiUntilMask_bp_intro
    (mask : CoPset) (label : ι)
    (k : ULift Unit → ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    Φ (.stopped label (k (.up ()))) ⊢
      wpiUntilMask H mask (vis (.inl (.bp label)) k) Φ := by
  simpa only [wpiUntilMask, untilBreakpoint_bp] using
    (wpiMask_ret H mask (.stopped label (k (.up ()))) Φ)

@[simp] theorem wpiUntilMask_vis
    (mask : CoPset) {α : Type u} (e : ε α)
    (k : α → ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntilMask H mask (vis (.inr e) k) Φ = iprop(
      |={mask, ∅}=> |={∅}=> H.handle e
        (fun a => wpiUntil H (k a)
          (fun result => iprop(|={∅, mask}=> Φ result)))
        (fun a => fupd ⊤ ∅ (wpiUntil H (k a) (fun _ => iprop(False))))) := by
  rw [wpiUntilMask, wpiMask, untilBreakpoint_vis, wpi_vis]
  rfl

/-- The usual sequencing syntax for a marker followed by a program. -/
@[simp] theorem wpiUntil_breakpoint_bind
    (label : ι)
    (k : ULift Unit → ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntil H ((ITree.translate SumE.inl (breakpoint label)).bind k) Φ =
      iprop(|={∅}=> Φ (.stopped label (k (.up ())))) := by
  simp only [breakpoint, trigger, ITree.translate_vis, ITree.translate_ret,
    ITree.bind_vis, ITree.bind_ret, wpiUntil_bp]

/-- Masked sequencing also stops before evaluating the continuation. -/
@[simp] theorem wpiUntilMask_breakpoint_bind
    (mask : CoPset) (label : ι)
    (k : ULift Unit → ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntilMask H mask ((ITree.translate SumE.inl (breakpoint label)).bind k) Φ =
      iprop(|={mask, ∅}=> |={∅}=> |={∅, mask}=>
        Φ (.stopped label (k (.up ())))) := by
  simp only [breakpoint, trigger, ITree.translate_vis, ITree.translate_ret,
    ITree.bind_vis, ITree.bind_ret, wpiUntilMask_bp]

/-- A breakpoint stops the calculation even when another breakpoint follows. -/
theorem wpiUntil_two_breakpoints
    (first second : ι) (rest : ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntil H (vis (.inl (.bp first)) (fun _ => vis (.inl (.bp second)) (fun _ => rest))) Φ =
      iprop(|={∅}=> Φ (.stopped first (vis (.inl (.bp second)) (fun _ => rest)))) :=
  wpiUntil_bp H first _ Φ

/-- The first marker also wins under a mask. -/
theorem wpiUntilMask_two_breakpoints
    (mask : CoPset) (first second : ι)
    (rest : ITree (BreakpointE ι + ε) ρ)
    (Φ : BreakpointResult ι ε ρ → PROP) :
    wpiUntilMask H mask
        (vis (.inl (.bp first)) (fun _ => vis (.inl (.bp second)) (fun _ => rest))) Φ =
      iprop(|={mask, ∅}=> |={∅}=> |={∅, mask}=>
        Φ (.stopped first (vis (.inl (.bp second)) (fun _ => rest)))) :=
  wpiUntilMask_bp H mask first _ Φ

/-- A trace is a branching tree, rather than a fixed list of markers.
The continuation of an ordinary event selects the trace for that response. -/
inductive TraceBreakpointE (ι : Type u) : Type u → Type (max u v) where
  | bp (label : ι) : TraceBreakpointE ι (ULift Unit)

abbrev BreakpointsTrace (ι : Type u) (ε : Type u → Type (max u v)) (ρ : Type uρ) :=
  ITree (TraceBreakpointE ι + ε) ρ

/-- Annotate every breakpoint with its label, preserving event continuations. -/
def markBreakpoints : (BreakpointE ι + ε) ⟶ (TraceBreakpointE ι + ε)
  | _, .inl (.bp label) => .inl (.bp label)
  | _, .inr event => .inr event

/-- Execute a trace plan while treating its markers as silent steps. -/
def replayBreakpoints (tr : BreakpointsTrace ι ε ρ) : ITree ε ρ :=
  .corecEmbed (fun tree =>
    match tree.dest with
    | ⟨.ret r, _⟩ => .inl (ret r)
    | ⟨.tau, k⟩ => .inr (tau' (.inr (k 0)))
    | ⟨.vis _ (.inl (.bp _)), k⟩ => .inr (tau' (.inr (k (.up ()))))
    | ⟨.vis _ (.inr e), k⟩ => .inr (vis' e (fun a => .inr (k a)))) tr

def wpiBreakpointsTrace (tr : BreakpointsTrace ι ε ρ) (Φ : ρ → PROP) : PROP :=
  wpi H (replayBreakpoints tr) Φ

private theorem replayBreakpoints_ret (r : ρ) :
    replayBreakpoints (ret r : BreakpointsTrace ι ε ρ) = ret r := by
  conv_lhs => simp only [replayBreakpoints]
  rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

private theorem replayBreakpoints_tau (t : BreakpointsTrace ι ε ρ) :
    replayBreakpoints (tau t) = tau (replayBreakpoints t) := by
  conv_lhs => simp only [replayBreakpoints]
  rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

private theorem replayBreakpoints_bp (i : ι)
    (k : ULift Unit → BreakpointsTrace ι ε ρ) :
    replayBreakpoints (vis (.inl (.bp i)) k) =
      tau (replayBreakpoints (k (.up ()))) := by
  conv_lhs => simp only [replayBreakpoints]
  rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

private theorem replayBreakpoints_vis {α : Type u} (e : ε α)
    (k : α → BreakpointsTrace ι ε ρ) :
    replayBreakpoints (vis (.inr e) k) =
      vis e (fun a => replayBreakpoints (k a)) := by
  conv_lhs => simp only [replayBreakpoints]
  rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

private theorem breakpointInter_ret (r : ρ) :
    breakpointInter (ret r : ITree (BreakpointE ι + ε) ρ) = ret r := by
  conv_lhs => simp only [breakpointInter]
  rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

private theorem breakpointInter_tau (t : ITree (BreakpointE ι + ε) ρ) :
    breakpointInter (tau t) = tau (breakpointInter t) := by
  conv_lhs => simp only [breakpointInter]
  rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

private theorem breakpointInter_bp (i : ι)
    (k : ULift Unit → ITree (BreakpointE ι + ε) ρ) :
    breakpointInter (vis (.inl (.bp i)) k) =
      tau (breakpointInter (k (.up ()))) := by
  conv_lhs => simp only [breakpointInter]
  rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

private theorem breakpointInter_vis {α : Type u} (e : ε α)
    (k : α → ITree (BreakpointE ι + ε) ρ) :
    breakpointInter (vis (.inr e) k) =
      vis e (fun a => breakpointInter (k a)) := by
  conv_lhs => simp only [breakpointInter]
  rw [PFunctor.M.unfold_corecEmbed]
  prove_unfold_lemma

/-- At a single breakpoint, continuing the erased tree is exactly the
postcondition required when the first segment stops. -/
theorem wpiUntil_bp_replay (label : ι)
    (k : ULift Unit → ITree (BreakpointE ι + ε) ρ) (Φ : ρ → PROP) :
    wpiUntil H (vis (.inl (.bp label)) k)
      (fun outcome => match outcome with
        | .returned r => Φ r
        | .stopped _ rest => wpi H (breakpointInter rest) Φ) =
      wpi H (breakpointInter (vis (.inl (.bp label)) k)) Φ := by
  rw [wpiUntil_bp, breakpointInter_bp, wpi_tau_step]

/-- The plan obtained from a source records each response-dependent branch. -/
theorem replay_markBreakpoints (t : ITree (BreakpointE ι + ε) ρ) :
    replayBreakpoints (ITree.translate (markBreakpoints (ι := ι) (ε := ε)) t) =
      breakpointInter t := by
  apply eq_of_bisim_state
      (lhs := fun t => replayBreakpoints (ITree.translate (markBreakpoints (ι := ι) (ε := ε)) t))
      (rhs := fun t => breakpointInter t)
  intro s
  apply s.dMatchOn
  · intro x hx
    rw [hx, ITree.translate_ret, replayBreakpoints_ret, breakpointInter_ret]
    exact .ret x
  · intro child ht
    rw [ht, ITree.translate_tau, replayBreakpoints_tau, breakpointInter_tau]
    exact .tau _ _ (Or.inr ⟨child, rfl, rfl⟩)
  · intro α e k hk
    cases e with
    | inl b =>
      cases b with
      | bp i =>
        rw [hk, ITree.translate_vis]
        change IEqF _ (replayBreakpoints (vis (.inl (.bp i)) _)) _
        rw [replayBreakpoints_bp, breakpointInter_bp]
        exact .tau _ _ (Or.inr ⟨k (.up ()), rfl, rfl⟩)
    | inr e =>
      rw [hk, ITree.translate_vis]
      change IEqF _ (replayBreakpoints (vis (.inr e) _)) _
      rw [replayBreakpoints_vis, breakpointInter_vis]
      exact .vis e _ _ (fun a => Or.inr ⟨k a, rfl, rfl⟩)

/-- A branch-dependent trace plan for the source has the same WP as erasure. -/
theorem wpiBreakpointsTrace_equiv (t : ITree (BreakpointE ι + ε) ρ)
    (Φ : ρ → PROP) :
    ∃ tr : BreakpointsTrace ι ε ρ,
      wpiBreakpointsTrace H tr Φ = wpi H (breakpointInter t) Φ := by
  exact ⟨ITree.translate (markBreakpoints (ι := ι) (ε := ε)) t,
    congrArg (fun tree => wpi H tree Φ) (replay_markBreakpoints t)⟩
end ProgramLogic

-- /-- The angelic handler requires only one successful continuation. -/
-- def angelicH {PROP : Type w} [BI PROP] : IHandlerBase PROP AngelicE where
--   handle e Φ _ := match e with
--     | .choose _ => iprop(∃ x, Φ x)
--   mono e := by
--     cases e
--     intro Φ Φ' spawned spawned'
--     istart
--     iintro HΦ _ HSome
--     icases HSome with ⟨%x, Hx⟩
--     iexists x
--     iapply HΦ
--     iexact Hx
--   ne := by
--     intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
--     cases e
--     exact exists_ne hΦ

-- instance angelicHSequential {PROP : Type w} [BI PROP] :
--     IHandler.Sequential (angelicH : IHandlerBase PROP AngelicE) where
--   sequential e Φ spawned := by
--     cases e
--     exact .rfl

-- /-- WP rule selecting a witness for an angelic choice. -/
-- theorem wpi_angelicChoice {PROP : Type w} [BI PROP] [BIFUpdate PROP]
--     (α : Type u) (chosen : α) (Φ : α → PROP) :
--     Φ chosen ⊢ wpi angelicH (angelicChoice α) Φ := by
--   rw [angelicChoice, trigger, wpi_vis]
--   istart
--   iintro Hchosen
--   imodintro
--   isimp only [angelicH]
--   iexists chosen
--   rw [wpi_ret]
--   imodintro
--   iexact Hchosen
