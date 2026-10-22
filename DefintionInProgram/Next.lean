import ProgramLogicCarte.WpiStructural
import DefintionInProgram.Breakpoint
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.FUpd
import Iris.Instances.Lib.Invariants
import Wander.Tactic
import Mathlib.Logic.Small.Defs

namespace ProgramLogic

open Iris Iris.BI ITree ProgramLogicCarte

universe u v uv

inductive NextE (ρ : Type u) : Type u → Type (max u v) where
  | next : NextE ρ (ULift Unit)
  | finish : NextE ρ ρ

def next {ρ : Type u} : ITree (NextE ρ) (ULift Unit) := trigger .next
def finish {ρ : Type u} : ITree (NextE ρ) ρ := trigger .finish


namespace NextGhost

variable {ι ρ : Type u} {ε : Type u → Type (max u v)} {GF : BundledGFunctors}
abbrev Tree (ι ρ : Type u) (ε : Type u → Type (max u v)) := ITree (BreakpointE.{u, v} ι + ε) ρ


variable [Inhabited (Tree ι ρ ε)]

namespace IrisUniv
open COFE OFE
abbrev constOF (B : Type*) : OFunctorPre := fun _ _ _ _ => B

instance oFunctorConstOF [COFE B] : OFunctor (constOF B) where
  ofe := _
  map _ _ := ⟨id, id_ne⟩
  map_ne := by intros; constructor; simp
  map_id := by simp
  map_comp := by simp

instance OFunctor.constOF_contractive [COFE B] : OFunctorContractive (constOF B) where
  map_contractive.1 := by simp [OFunctor.map]

end IrisUniv


/-- Client ownership of the suspended computation. -/
abbrev owns (γ : GName) (t : ITree (BreakpointE ι + ε) ρ) : IProp GF :=
  -- ghost_var γ (.own ⟨1 / 3, by grind⟩) (equivShrink _ t)
  iOwn (F := IrisUniv.constOF (DFracAgree.DFracAgreeR (DiscreteO (Tree ι ρ ε)))) γ (mk ⟨1 / 3, by grind⟩ ⟨t⟩)

instance {γ} {t : ITree (BreakpointE ι + ε) ρ} : Timeless (owns (GF := GF) γ t) := by
  unfold owns
  infer_instance

theorem agreement (γ : GName) (t s : ITree (BreakpointE ι + ε) ρ) :
    iprop(owns (GF := GF) γ t ∗ owns γ s) ⊢ iprop(⌜t = s⌝) := by
  unfold owns
  iintro ⟨Ht, Hs⟩
  ihave %heq := ghost_var_agree $$ Ht Hs
  ipureintro
  exact (equivShrink _).injective heq
variable {hlc : HasLC} [InvGS_gen hlc GF]


/-- The scheduler's half is existentially hidden in an invariant. The only
unshared half returned to the monitor is `owns`. -/
def schedulerInv (N : Namespace) (γ : GName) (t : Tree ι ρ ε) : IProp GF :=
  iprop(inv N (iprop(∃ (t : Tree ι ρ ε), owns (GF := GF) γ t)))

/-- The only update used by the `next` protocol requires both matching halves. -/
private theorem advance (γ : GName) (t s : ITree (BreakpointE ι + ε) ρ) :
    iprop(owns (GF := GF) γ t ∗ owns γ t ∗ owns γ t) ⊢
      iprop(|={∅}=> owns γ s ∗ owns γ s ∗ owns γ s) := by
  unfold owns
  iintro ⟨Ht, Hc⟩
  imod ghost_var_update_2 (equivShrink _ s) γ (equivShrink _ t) (equivShrink _ t) $$ Ht Hc with H
  imodintro
  iexact H



/-- A `next` must reach a breakpoint; normal termination is handled by `finish`. -/
def handle (H : IHandlerBase (IProp GF) ε) (N : Namespace) (γ : GName)
    (Φ : ULift Unit → IProp GF) : IProp GF :=
  iprop(∀ t : ITree (BreakpointE ι + ε) ρ, schedulerInv N γ t ={∅}=∗
    |={N, ∅}=> wpiUntil H t (fun outcome => match outcome with
      | .returned _ => iprop(False)
      | .stopped _ rest => iprop(|={∅, N}=> schedulerInv N γ rest ∗ Φ (.up ()))))


-- /-- Client rule: run the owned segment, then return the updated client token.
-- The scheduler half is supplied by `handle`, rather than assumed by the client. -/
-- theorem next_rule (H : IHandlerBase (IProp GF) ε) (N : Namespace) (γ : GName)
--     (t : ITree (BreakpointE ι + ε) ρ) (Φ : ULift Unit → IProp GF) :
--     iprop(wpiUntil H t (fun outcome => match outcome with
--       | .returned _ => iprop(False)
--       | .stopped _ rest => iprop(Φ (.up ())))) ⊢ handle (ι := ι) (ρ := ρ) H N γ Φ := by
--   isimp [handle, schedulerInv]
--   -- iintro ⟨Hclient, Hwp⟩
--   iintro Hwp
--   iintro %s Hauth
--   imodintro
--   icases Iris.BI.persistent_and_sep.mp $$ Hauth with ⟨Hauth, HQ⟩
--   unfold wpiUntil at *
--   ihave %heq : ⌜s = t⌝ $$ [Hauth HQ]
--   ·
--     iapply agreement γ s t
--     icases Hauth with ⟨$, -⟩
--     iframe
--   iapply wpi_wand $$ Hwp
--   iinv HQ with Hclient
  -- isimp
  -- imodintro
  -- icases BI.later_intro $$ Hauth with Hauth
  -- isimp
  -- -- icases BI.except0_exists.mp $$ Hclient with Hclient
  -- icases Hclient with ⟨%t, Hclient⟩
  -- imod Hclient with Hclient
  -- ihave %heq : ⌜s = t⌝ $$ [Hauth Hclient]
  -- · iapply agreement γ s t
  --   icases Hauth with ⟨$, -⟩
  --   iframe
  -- subst s
  -- unfold wpiUntil at *
  -- -- icases Iris.BI.persistent_and_sep.mp $$ Hclient with ⟨Hclient, HQ⟩


  -- iapply wpi_wand $$ [Hauth Hclient] Hwp
  -- iintro %outcome Hpost
  -- cases outcome with
  -- | returned r => iexact Hpost
  -- | stopped label rest =>
  --   isimp only at Hpost
  --   isimp only
  --   imodintro
  --   iframe Hpost
  --   ispecialize Hpost $$ Hclient

  --   icases Hpost with ⟨Hpost, $⟩
  --   -- ihave Hauthclient' : owns γ rest ∗ (authority γ rest ∧ inv N (iprop(∃ t, authority γ t))) $$ [Hauth Hclient]
  --   -- · isimp [BI.and_sep_plainly]
  --   imod advance γ t rest $$ [$Hauth $Hclient] with ⟨Hauth, Hclient⟩
  --   imodintro
  --   iframe Hauth
  --   iapply Hpost $$ Hclient

/-- Finishing runs the remaining source tree to completion and returns its value. -/
def handleFinish (H : IHandlerBase (IProp GF) ε) (N : Namespace) (γ : GName)
    (Φ : ρ → IProp GF) : IProp GF :=
  iprop(∀ t : Tree ι ρ ε, schedulerInv N γ t -∗
    wpiUntil H t (fun outcome => match outcome with
      | .returned r => iprop(|={N, ∅}=> schedulerInv N γ (ret r : Tree ι ρ ε) ∗ Φ r)
      | .stopped _ _ => iprop(False)))

-- /-- The client supplies the matching ownership and a terminal source VC. -/
-- theorem finish_rule (H : IHandlerBase (IProp GF) ε) (γ : GName)
--     (t : Tree ι ρ ε) (Φ : ρ → IProp GF) :
--     iprop(owns γ t ∗ wpiUntil H t (fun outcome => match outcome with
--       | .returned r => iprop(owns γ (ret r : Tree ι ρ ε) -∗ Φ r)
--       | .stopped _ _ => iprop(False))) ⊢ handleFinish (ι := ι) H γ Φ := by
--   iintro ⟨Hclient, Hwp⟩
--   unfold handleFinish
--   iintro %s Hauth
--   ihave %heq := agreement γ s t $$ [$Hauth $Hclient]
--   subst s
--   unfold wpiUntil at *
--   iapply wpi_wand $$ [Hauth Hclient] Hwp
--   iintro %outcome Hpost
--   cases outcome with
--   | returned r =>
--     imod advance γ t (.ret r) $$ [$Hauth $Hclient] with ⟨Hauth, Hclient⟩
--     imodintro
--     iframe Hauth
--     iapply Hpost $$ Hclient
--   | stopped label rest => iexact Hpost


/-- Invariant-backed logical handler, with the same state-passing shape as
`stateH`: each operation takes the current interpretation and returns its
successor. Unlike `legacyHandler`, it does not hand out the private half. -/
def handler (ι : Type) (ε : Type → Type) {ρ : Type}
    [Small.{0} (Tree ι ρ ε)] [GhostVarG GF (Shrink.{0} (Tree ι ρ ε))]
    (N : Namespace) (H : IHandlerBase (IProp GF) ε) (γ : GName) :
    IHandlerBase (IProp GF) (NextE ρ) where
  handle e Φ _ := match e with
    | .next => handle (ι := ι) (ρ := ρ) H N γ Φ
    | .finish => handleFinish (ι := ι) (ρ := ρ) H N γ Φ
  mono e := sorry
  ne := sorry

instance (N : Namespace) (H : IHandlerBase (IProp GF) ε) (γ : GName) :
    IHandler.Sequential (handler (ρ := ρ) ι ε N H γ) where
  sequential e Φ spawned := by cases e <;> exact .rfl

/-- Candidate adequacy statement, currently *false* without a simulation
condition that rules out raw ghost updates. For example, with an outer
`wpiMask (↑N)`, a monitor that immediately returns can open `schedulerInv`,
update both halves from `ret false` to `ret true`, then claim the latter as its
result without executing the source tree. This is kept as a concrete target for
revising the protocol, not as a theorem or a proof obligation to admit. -/
def monitorAdequacyGoal (N : Namespace) (H : IHandlerBase (IProp GF) ε)
    (initial : Tree ι ρ ε) (monitor : ITree (NextE ρ) α)
    (Φ : ρ → IProp GF) : Prop :=
  ∀ γ : GName,
    iprop(schedulerInv (ι := ι) (ρ := ρ) (ε := ε) N γ ∗ owns γ initial ∗
      wpiMask (handler (ρ := ρ) ι ε N H γ) (↑N) monitor
        (fun _ => iprop(∃ r, owns γ (ret r : Tree ι ρ ε) ∗ Φ r))) ⊢
      wpiMask H (↑N) (breakpointInter initial) Φ


namespace Example

/-- The source consists of two markers and then returns `r`. -/
def source₁ (second : ι) (r : ρ) : Tree ι ρ ε :=
  vis (.inl (.bp second)) (fun _ => ret r)

def source₀ (first second : ι) (r : ρ) : Tree ι ρ ε :=
  vis (.inl (.bp first)) (fun _ => source₁ second r)

/-- One remaining controller step, and the complete two-step controller. -/
def controller₁ : ITree (NextE ρ) ρ := (next (ρ := ρ)).bind (fun _ => finish (ρ := ρ))

def controller : ITree (NextE ρ) ρ := (next (ρ := ρ)).bind (fun _ => controller₁ (ρ := ρ))
#check wpiUntil_breakpoint_bind
omit [Small.{0} (Tree ι ρ ε)]
  [GhostVarG GF (Shrink.{0} (Tree ι ρ ε))] [Inhabited (Tree ι ρ ε)]  in
theorem source₀_segment (H : IHandlerBase (IProp GF) ε) (first second : ι) (r : ρ)
    (Ψ : BreakpointResult ι ε ρ → IProp GF) :
    wpiUntil H (source₀ (ε := ε) first second r) Ψ =
      iprop(|={∅}=> Ψ (.stopped first (source₁ (ε := ε) second r))) := by
  unfold source₀
  rw [wpiUntil_bp]
#check fupd_except0
omit [Small.{0} (Tree ι ρ ε)]
  [GhostVarG GF (Shrink.{0} (Tree ι ρ ε))] [Inhabited (Tree ι ρ ε)] in
theorem source₁_segment (H : IHandlerBase (IProp GF) ε) (second : ι) (r : ρ)
    (Ψ : BreakpointResult ι ε ρ → IProp GF) :
    wpiUntil H (source₁ (ε := ε) second r) Ψ = iprop(|={∅}=> Ψ (.stopped second (ret r))) := by
  unfold source₁
  rw [wpiUntil_bp]
-- #check BI.persistent_and_sep
/-- Reduced client VC for the second call. -/
theorem controller₁_client_vc {N} {H : IHandlerBase (IProp GF) ε} {γ : GName}
    {second : ι} {r : ρ} {Φ : ρ → IProp GF} :
    iprop(
      owns γ (source₁ (ε := ε) second r) ∗ Φ r ⊢
      wpi (handler (ρ := ρ) ι ε N H γ) (controller₁ (ρ := ρ)) Φ) := by
  unfold controller₁
  -- iintro ⟨Hsource, Hcont⟩
  iintro ⟨Hs, Hpost⟩
  unfold next
  isimp [ITree.bind_vis, ITree.bind_ret]
  nth_rw 1 [handler]
  isimp only
  nth_rw 1 [handle]
  imodintro
  unfold schedulerInv
  iintro %t Hinv
  imodintro
  iinv Hinv with Hinv
  isimp
  icases Timeless.timeless $$ Hinv with Hinv
  iapply fupd_except0
  imodintro
  imod Hinv
  imodintro
  ihave %agree : ⌜t = _⌝  $$ [Hs Hinv]
  · iapply agreement $$ [Hs Hinv]
    iframe
  subst agree
  icases BI.later_intro $$ Hinv with Hinv
  iframe Hinv
  isimp [source₁_segment]
  iapply fupd_intro
  iapply fupd_mask_intro_subseteq
  · simp
  ·

  -- isimp
  -- imodintro
  -- isimp
  -- imodintro
  -- iapply wpi_bind
  -- iapply wpi_next_bind H γ (source₁ (ε := ε) second r)
  -- rw [source₁_segment]
  -- iframe Hsource
  -- imodintro
  -- iintro Hfinished
  -- iapply wpi_finish H γ (ret r)
  -- iframe Hfinished
  -- rw [wpiUntil_ret]
  -- imodintro
  -- iintro Hret
  -- iapply Hcont $$ Hret

/-- Reduced client VC for the first call. -/
theorem controller_client_vc (H : IHandlerBase (IProp GF) ε) (γ : GName)
    (first second : ι) (r : ρ) (Φ : ρ → IProp GF) :
    iprop(owns γ (source₀ (ε := ε) first second r) ∗
      |={∅}=> (owns γ (source₁ (ε := ε) second r) -∗ wpi (legacyHandler (ρ := ρ) ι ε H γ) (controller₁ (ρ := ρ)) Φ)) ⊢
      wpi (legacyHandler (ρ := ρ) ι ε H γ) (controller (ρ := ρ)) Φ := by
  unfold controller
  iintro Hpre
  iapply wpi_next_bind H γ (source₀ (ε := ε) first second r)
  rw [source₀_segment]
  iexact Hpre

/-- Two `next`s consume the breakpoints; `finish` returns the source's result. -/
theorem controller_spec (H : IHandlerBase (IProp GF) ε) (γ : GName)
    (first second : ι) (r : ρ) :
    owns (GF := GF) γ (source₀ (ε := ε) first second r) ⊢
      wpi (legacyHandler (ρ := ρ) ι ε H γ) (controller (ρ := ρ))
        (fun result => iprop(⌜result = r⌝ ∗ owns γ (ret result : Tree ι ρ ε))) := by
  iintro Hsource
  iapply controller_client_vc H γ first second r
  iframe Hsource
  imodintro
  iintro Hsource
  iapply controller₁_client_vc H γ second r
  iframe Hsource
  iintro Hfinished
  isplitr
  · ipureintro
    rfl
  · iexact Hfinished

/-- `next` (rather than `finish`) on a terminated source has an unsatisfiable VC. -/
theorem finished_segment_vc (H : IHandlerBase (IProp GF) ε) (γ : GName)
    (r : ρ) (Φ : ULift Unit → IProp GF) :
    wpiUntil H (ret r : Tree ι ρ ε) (fun outcome => match outcome with
      | .returned _ => iprop(False)
      | .stopped _ rest => iprop(owns γ rest -∗ Φ (.up ()))) =
      iprop(|={∅}=> False) := by
  rw [wpiUntil_ret]

end Example

end

def Assoc (op : S -> S -> S) : Prop := ∀ a b c, op (op a b) c = op a (op b c)
def IsUnit (op : S -> S -> S) (e : S) : Prop := ∀ x, op e x = x ∧ op x e = x
theorem inv_unique (op) (e x y₁ y₂ : S) (ha : Assoc op) (he : IsUnit op e) (h₁ : op y₁ x = e) (h₂ : op x y₂ = e) : y₁ = y₂ := by
  unfold IsUnit Assoc at *
  calc
    y₁ = op y₁ e := by grind
    _ = op y₁ (op x y₂) := by grind
    _ = op (op y₁ x) y₂ := by grind
    _ = _ := by grind

end NextGhost
end ProgramLogic
