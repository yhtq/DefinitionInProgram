import Lean
import Iris.Instances.Lib.GhostVar
import Iris.Instances.Lib.FUpd
import Iris.Instances.Lib.Invariants

/-! Proof-mode helpers for fractional ghost-variable ownership.

Fractionality alone does not imply either agreement or an update operation.
The default tactics use the `ghost_var` laws. The `using` forms accept laws for
other ownership families, provided their rule has the same argument order as
`ghost_var_agree` or `ghost_var_update_2`. An update requires the selected
fractions to add up to the whole ownership. The unannotated list form reads
fractions from the selected spatial hypotheses, unfolding simple wrappers
around `ghost_var` when necessary. -/

open Iris Iris.BI

/-- Derive a pure equality from two spatial `ghost_var` hypotheses without
consuming them. Both must refer to the same ghost name. -/
macro "frac_agree " left:specPat right:specPat " as " result:icasesPat : tactic =>
  `(tactic| ihave $result := Iris.ghost_var_agree $$ $left $right)

/-- Use an explicit agreement law for another fractional ownership family.
The rule must take the selected spatial hypotheses through `$$`. -/
macro "frac_agree " left:specPat right:specPat " using " rule:term
    " as " result:icasesPat : tactic =>
  `(tactic| ihave $result := ($rule) $$ $left $right)

/-- Compare each subsequent spatial `ghost_var` with the first one without
consuming any ownership. Produces one ordinary Lean equality per subsequent
hypothesis. For example: `frac_agree [H₀, H₁, H₂] as [eq₁, eq₂]`.
Requires at least two inputs and exactly one equality name per comparison. -/
macro "frac_agree" "[" hyps:ident,* "]" "as" "[" eqs:ident,* "]" : tactic => do
  let hyps := hyps.getElems
  let eqs := eqs.getElems
  if hyps.size < 2 || eqs.size + 1 != hyps.size then
    Lean.Macro.throwError "frac_agree requires at least two hypotheses and exactly one equality name per remaining hypothesis"
  let base ← `(specPat| $(hyps[0]!):ident)
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  for i in [1:hyps.size] do
    let other ← `(specPat| $(hyps[i]!):ident)
    let pat ← `(icasesPat| %$(eqs[i - 1]!):ident)
    steps := steps.push (← `(tactic|
      ihave $pat := Iris.ghost_var_agree $$ $base $other))
  `(tactic| ( $steps:tactic* ))

/-- Update two fractional `ghost_var` assertions together. `next` is the new
stored value. `left'` and `right'` name the two updated spatial hypotheses.
The tactic leaves the fraction equation `q₁ + q₂ = 1` as an explicit proof
goal, rather than assuming that any fractions can be updated. -/
macro "frac_update " left:specPat right:specPat " to " next:term
    " with " pat:icasesPat : tactic =>
  `(tactic|
    imod (Iris.ghost_var_update_2 $next _ _ _ _ _ ?_) $$ $left $right
      with $pat)

/-- Use a custom two-resource update law whose first argument is the new
value, followed by inferable ownership parameters and a final fraction-sum
proof. Like `frac_update`, this exposes that proof as a separate Lean goal. -/
macro "frac_update " left:specPat right:specPat " to " next:term
    " using " rule:term " with " pat:icasesPat : tactic =>
  `(tactic| imod ($rule $next _ _ _ _ _ ?_) $$ $left $right with $pat)

/-- Update at least two selected spatial `ghost_var` hypotheses in an update or
fupd goal, naming each updated hypothesis. The optional annotations must match the
selected fractions. Leaves the left-associated equation `q₁ + ... + qₙ = 1`
as an explicit Lean goal; no fraction equation is discharged automatically.
For example: `frac_update [H₁ : q₁, H₂ : q₂, H₃ : q₃] to b with [H₁', H₂', H₃']`. -/
syntax fracEntry := ident ":" term
open Lean

macro "frac_update" "[" entries:fracEntry,* "]" "to" next:term
    "with" "[" names:ident,* "]" : tactic => do
    let entries := entries.getElems
    let names := names.getElems
    if entries.size < 2 || entries.size != names.size then
      Macro.throwError "frac_update requires at least two hypotheses and one output name per hypothesis"
    let hs := entries.map (·.raw[0]!)
    let qs := entries.map (·.raw[2]!)
    let mut steps : Array (TSyntax `tactic) := #[]
    let mut total : TSyntax `term := ⟨qs[0]!⟩
    let mut combined : TSyntax `ident := ⟨hs[0]!⟩
    for i in [1:entries.size - 1] do
      let h : TSyntax `ident := ⟨hs[i]!⟩
      let fresh := mkIdent (Name.mkSimple s!"fracCombined{i}")
      let sel1 ← `(selPat| $combined:ident)
      let sel2 ← `(selPat| $h:ident)
      let pat ← `(icasesPat| $fresh:ident)
      steps := steps.push (← `(tactic| icombine $sel1 $sel2 as $pat))
      combined := fresh
      let qi : TSyntax `term := ⟨qs[i]!⟩
      total := (← `(term| $total + $qi))
    let last : TSyntax `ident := ⟨hs[entries.size - 1]!⟩
    let lastQ : TSyntax `term := ⟨qs[entries.size - 1]!⟩
    let fresh := if entries.size == 2 then (⟨names[0]!⟩ : TSyntax `ident) else
      mkIdent `fracUpdatedCombined
    let lastName : TSyntax `ident := ⟨names[names.size - 1]!⟩
    let selected ← `(specPat| $combined:ident)
    let selectedLast ← `(specPat| $last:ident)
    let out1 ← `(Iris.ProofMode.icasesPatAlts| $fresh:ident)
    let out2 ← `(Iris.ProofMode.icasesPatAlts| $lastName:ident)
    steps := steps.push (← `(tactic|
      imod (Iris.ghost_var_update_2 $next _ _ $total _ $lastQ ?_) $$
        $selected $selectedLast with ⟨$out1, $out2⟩))
    -- `imod` puts the fraction equation first; split only the updated spatial goal.
    steps := steps.push (← `(tactic| rotate_left 1))
    let mut current := fresh
    for i in [:entries.size - 2] do
      let idx := entries.size - 2 - i
      let mut leftSum : TSyntax `term := ⟨qs[0]!⟩
      for j in [1:idx] do
        let qj : TSyntax `term := ⟨qs[j]!⟩
        leftSum := (← `(term| $leftSum + $qj))
      let q : TSyntax `term := ⟨qs[idx]!⟩
      let left := if idx == 1 then (⟨names[0]!⟩ : TSyntax `ident) else
        mkIdent (Name.mkSimple s!"fracUpdated{idx}")
      let right : TSyntax `ident := ⟨names[idx]!⟩
      let selected ← `(specPat| $current:ident)
      let out1 ← `(Iris.ProofMode.icasesPatAlts| $left:ident)
      let out2 ← `(Iris.ProofMode.icasesPatAlts| $right:ident)
      steps := steps.push (← `(tactic|
        icases (Iris.ghost_var_split _ $next $leftSum $q) $$ $selected
          with ⟨$out1, $out2⟩))
      current := left
    -- Restore the equation as the first goal for the caller.
    steps := steps.push (← `(tactic| rotate_right 1))
    `(tactic| ( $steps:tactic* ))

/-- Infer the fractions from the selected spatial `ghost_var` hypotheses, without
annotations: `frac_update [H₁, H₂] to b with [H₁', H₂']`.
The selected hypotheses must all own the same ghost name with `.own` fractions. -/
elab "frac_update" "[" hyps:ident,* "]" "to" next:term
    "with" "[" names:ident,* "]" : tactic => do
  let hs := hyps.getElems
  let ns := names.getElems
  if hs.size < 2 || hs.size != ns.size then
    Lean.throwError "frac_update requires at least two hypotheses and one output name per hypothesis"
  let mvar ← Lean.Elab.Tactic.getMainGoal
  mvar.withContext do
    let some ig := Iris.ProofMode.parseIrisGoal? (← mvar.getType) |
      Lean.throwError "frac_update: expected an Iris proof-mode goal with spatial hypotheses"
    let mut entries : Array (Lean.TSyntax `fracEntry) := #[]
    let mut ghostName : Option Lean.Expr := none
    for h in hs do
      let ivar ← ig.hyps.findWithInfo h
      let some (_, _, spatial, ty) := ig.hyps.getDecl? ivar |
        Lean.throwError m!"frac_update: unknown hypothesis {h}"
      unless spatial.isConstOf ``Bool.false do
        Lean.throwError m!"frac_update: {h} must be a spatial hypothesis"
      let mut ty := (← Lean.instantiateMVars ty).consumeMData
      -- First inspect the original head; only unfold a wrapper if necessary.
      unless ty.isAppOf ``Iris.ghost_var do
        ty ← Lean.Meta.whnf ty
      ty := ty.consumeMData
      let some #[_, _, _, gamma, dq, _] := ty.appM? ``Iris.ghost_var |
        Lean.throwError m!"frac_update: {h} is not a ghost_var ownership hypothesis: {ty}"
      let mut dq := (← Lean.instantiateMVars dq).consumeMData
      unless dq.isAppOf ``Iris.DFrac.own do
        dq ← Lean.Meta.whnf dq
      let some #[q] := dq.appM? ``Iris.DFrac.own |
        Lean.throwError m!"frac_update: {h} must contain an .own fraction"
      if let some previous := ghostName then
        unless ← Lean.Meta.isDefEq previous gamma do
          Lean.throwError m!"frac_update: {h} owns a different ghost name"
      else
        ghostName := some gamma
      let qStx ← Lean.PrettyPrinter.delab q
      entries := entries.push (← `(fracEntry| $h:ident : $(⟨qStx⟩):term))
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      frac_update [$entries:fracEntry,*] to $next with [$ns:ident,*]))

section FractionalManyExamples

-- A different ghost name and a non-`.own` resource must not be accepted.
example {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    {A : Type} [GhostVarG GF A]
    (γ δ : GName) (a b : A) (q₁ q₂ r : Qp) (hfull : q₁ + q₂ = 1) :
    (iprop(ghost_var (GF := GF) γ (.own q₁) a ∗
      ghost_var γ (.own q₂) a ∗ ghost_var δ (.own r) a ∗
      ghost_var γ .discard a) : IProp GF) ⊢
      iprop(|={∅}=> ghost_var γ (.own q₁) b ∗ ghost_var γ (.own q₂) b ∗
        ghost_var δ (.own r) a ∗ ghost_var γ .discard a) := by
  iintro ⟨H₁, H₂, Hother, Hdiscarded⟩
  fail_if_success (frac_update [H₁, Hother] to b with [X, Y])
  fail_if_success (frac_update [H₁, Hdiscarded] to b with [X, Y])
  frac_update [H₁, H₂] to b with [H₁', H₂']
  · exact hfull
  imodintro
  iframe

example {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    {A : Type} [GhostVarG GF A]
    (γ : GName) (a b : A) (q₁ q₂ : Qp) (hfull : q₁ + q₂ = 1) :
    (iprop(ghost_var (GF := GF) γ (.own q₁) a ∗ ghost_var γ (.own q₂) a) : IProp GF) ⊢
      iprop(|={∅}=> ghost_var γ (.own q₁) b ∗ ghost_var γ (.own q₂) b) := by
  iintro ⟨H₁, H₂⟩
  frac_update [H₁, H₂] to b with [H₁', H₂']
  · show q₁ + q₂ = 1
    exact hfull
  imodintro
  iframe

example {GF : BundledGFunctors} {A : Type} [GhostVarG GF A]
    (γ : GName) (a₀ a₁ a₂ : A) (q₀ q₁ q₂ : Qp) :
    (iprop(ghost_var (GF := GF) γ (.own q₀) a₀ ∗
      ghost_var γ (.own q₁) a₁ ∗ ghost_var γ (.own q₂) a₂) : IProp GF) ⊢
      iprop(⌜a₀ = a₁ ∧ a₀ = a₂⌝ ∧
        (ghost_var γ (.own q₀) a₀ ∗ ghost_var γ (.own q₁) a₁ ∗
          ghost_var γ (.own q₂) a₂)) := by
  iintro ⟨H₀, H₁, H₂⟩
  frac_agree [H₀, H₁, H₂] as [eq₁, eq₂]
  isplit
  · ipureintro
    exact ⟨eq₁, eq₂⟩
  · iframe

example {GF : BundledGFunctors} {A : Type} [GhostVarG GF A]
    (γ : GName) (a₀ a₁ a₂ a₃ : A) (q₀ q₁ q₂ q₃ : Qp) :
    (iprop(ghost_var (GF := GF) γ (.own q₀) a₀ ∗
      ghost_var γ (.own q₁) a₁ ∗ ghost_var γ (.own q₂) a₂ ∗
      ghost_var γ (.own q₃) a₃) : IProp GF) ⊢
      iprop(⌜a₀ = a₁ ∧ a₀ = a₂ ∧ a₀ = a₃⌝ ∧
        (ghost_var γ (.own q₀) a₀ ∗ ghost_var γ (.own q₁) a₁ ∗
          ghost_var γ (.own q₂) a₂ ∗ ghost_var γ (.own q₃) a₃)) := by
  iintro ⟨H₀, H₁, H₂, H₃⟩
  frac_agree [H₀, H₁, H₂, H₃] as [eq₁, eq₂, eq₃]
  isplit
  · ipureintro
    exact ⟨eq₁, eq₂, eq₃⟩
  · iframe

example {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    {A : Type} [GhostVarG GF A]
    (γ : GName) (a b : A) (q₁ q₂ q₃ : Qp)
    (hfull : q₁ + q₂ + q₃ = 1) :
    (iprop(ghost_var (GF := GF) γ (.own q₁) a ∗
      ghost_var γ (.own q₂) a ∗ ghost_var γ (.own q₃) a) : IProp GF) ⊢
      iprop(|={∅}=> ghost_var γ (.own q₁) b ∗
        ghost_var γ (.own q₂) b ∗ ghost_var γ (.own q₃) b) := by
  iintro ⟨H₁, H₂, H₃⟩
  frac_update [H₁, H₂, H₃] to b with [H₁', H₂', H₃']
  · show q₁ + q₂ + q₃ = 1
    exact hfull
  imodintro
  iframe

example {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    {A : Type} [GhostVarG GF A]
    (γ : GName) (a b : A) (q₁ q₂ q₃ q₄ : Qp)
    (hfull : q₁ + q₂ + q₃ + q₄ = 1) :
    (iprop(ghost_var (GF := GF) γ (.own q₁) a ∗
      ghost_var γ (.own q₂) a ∗ ghost_var γ (.own q₃) a ∗
      ghost_var γ (.own q₄) a) : IProp GF) ⊢
      iprop(|={∅}=> ghost_var γ (.own q₁) b ∗
        ghost_var γ (.own q₂) b ∗ ghost_var γ (.own q₃) b ∗
        ghost_var γ (.own q₄) b) := by
  iintro ⟨H₁, H₂, H₃, H₄⟩
  frac_update [H₁, H₂, H₃, H₄] to b with [H₁', H₂', H₃', H₄']
  · show q₁ + q₂ + q₃ + q₄ = 1
    exact hfull
  imodintro
  iframe

end FractionalManyExamples
