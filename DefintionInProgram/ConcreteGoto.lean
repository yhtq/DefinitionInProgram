import DefintionInProgram.SourceLanguage

/-!
# A goto language with program-specific program counters

There is no `Program` wrapper and no `run` command. A program is an `Expr`.
A block is a labelled expression whose body is normally assembled from
ordinary statements with `Expr.seq`.

`GotoLanguage ι Next` is an information-free tag reserved for the eventual
`SourceLanguage` instance. Program-specific control-flow information belongs
to the concrete type `ι` and its concrete `IsPC` instance.
-/

namespace ConcreteGoto


abbrev Var := Nat
abbrev Store := Var → Int

structure State (ι : Type*) where
  store : Store
  pc : ι

def State.withVar (s : State ι) (x : Var) (value : Int) : State ι :=
  { s with store := Function.update s.store x value }

def State.withPC (s : State ι) (pc : ι) : State ι :=
  { s with pc := pc }

/-- A `next` token denotes only a state relation, not an operation or program. -/
class NextMeaning (ι : Type*) (Next : Type*) where
  step : Next → State ι → State ι → Prop

instance : NextMeaning ι Empty where
  step token := nomatch token

/-- Source programs instantiate `Next` with `Empty`; verification programs
    use the separate `MExpr` syntax below. -/
inductive Expr (ι : Type*) (Next : Type*) where
  | skip
  | assign (x : Var) (rhs : Store → Int)
  | goto (target : ι)
  | seq (first second : Expr ι Next)
  | choice (left right : Expr ι Next)
  | ite (guard : State ι → Bool) (ifTrue ifFalse : Expr ι Next)
  | while (guard : State ι → Bool) (body : Expr ι Next)
  | block (label : ι) (body : Expr ι Next)
  | next (operation : Next)

namespace Expr

scoped infixr:60 " ;; " => Expr.seq

/-- Finite big-step operational semantics. A block is enabled exactly when
its label is the current `pc`; a choice of labelled blocks is a dispatcher. -/
inductive BigStep [NextMeaning ι Next] :
    Expr ι Next → State ι → State ι → Prop
  | skip : BigStep .skip s s
  | assign : BigStep (.assign x rhs) s (s.withVar x (rhs s.store))
  | goto : BigStep (.goto target) s (s.withPC target)
  | seq (first : BigStep e₁ s middle) (second : BigStep e₂ middle t) :
      BigStep (.seq e₁ e₂) s t
  | choiceLeft (run : BigStep left s t) :
      BigStep (.choice left right) s t
  | choiceRight (run : BigStep right s t) :
      BigStep (.choice left right) s t
  | iteTrue {guard : State ι → Bool} (condition : guard s = true)
      (run : BigStep ifTrue s t) :
      BigStep (.ite guard ifTrue ifFalse) s t
  | iteFalse {guard : State ι → Bool} (condition : guard s = false)
      (run : BigStep ifFalse s t) :
      BigStep (.ite guard ifTrue ifFalse) s t
  | whileFalse {guard : State ι → Bool} (condition : guard s = false) :
      BigStep (.while guard body) s s
  | whileTrue {guard : State ι → Bool} (condition : guard s = true)
      (bodyStep : BigStep body s middle)
      (rest : BigStep (.while guard body) middle t) :
      BigStep (.while guard body) s t
  | block (atLabel : s.pc = label) (run : BigStep body s t) :
      BigStep (.block label body) s t
  | next (run : NextMeaning.step operation s t) : BigStep (.next operation) s t

/-- Adapter to `SourceLanguage`'s result shape; expressions return `Unit`. -/
def Sem [NextMeaning ι Next]
    (e : Expr ι Next) (s : State ι) (final : Unit × State ι) : Prop :=
  final.1 = () ∧ BigStep e s final.2

/-! ## Execution traces -/

/-- Expressions treated as one trace unit. In particular, a labelled block
is atomic even though its body may be a long sequence. -/
inductive TraceUnit : Expr ι Next → Prop
  | skip : TraceUnit .skip
  | assign : TraceUnit (.assign x rhs)
  | goto : TraceUnit (.goto target)
  | while {guard : State ι → Bool} : TraceUnit (.while guard body)
  | block {label : ι} : TraceUnit (.block label body)
  | next : TraceUnit (.next operation)

/-- Trace extraction inside one dispatcher iteration. `choice` and `ite` are
transparent, while blocks remain atomic units. -/
inductive AtomicTrace [NextMeaning ι Next] :
    Expr ι Next → State ι → State ι →
      List (Expr ι Next × State ι) → Prop
  | unit (isUnit : TraceUnit e) (run : BigStep e s t) :
      AtomicTrace e s t [(e, s)]
  | seq (first : AtomicTrace e₁ s middle tr₁)
      (second : AtomicTrace e₂ middle t tr₂) :
      AtomicTrace (.seq e₁ e₂) s t (tr₁ ++ tr₂)
  | choiceLeft (run : AtomicTrace left s t tr) :
      AtomicTrace (.choice left right) s t tr
  | choiceRight (run : AtomicTrace right s t tr) :
      AtomicTrace (.choice left right) s t tr
  | iteTrue {guard : State ι → Bool} (condition : guard s = true)
      (run : AtomicTrace ifTrue s t tr) :
      AtomicTrace (.ite guard ifTrue ifFalse) s t tr
  | iteFalse {guard : State ι → Bool} (condition : guard s = false)
      (run : AtomicTrace ifFalse s t tr) :
      AtomicTrace (.ite guard ifTrue ifFalse) s t tr

theorem AtomicTrace.exists_of_bigStep
    {ι Next : Type*} {e : Expr ι Next} {s t : State ι}
    [NextMeaning ι Next]
    (run : BigStep e s t) : ∃ tr, AtomicTrace e s t tr := by
  induction run with
  | skip => exact ⟨_, .unit .skip .skip⟩
  | assign => exact ⟨_, .unit .assign .assign⟩
  | goto => exact ⟨_, .unit .goto .goto⟩
  | seq _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨tr₁, h₁⟩
      rcases ih₂ with ⟨tr₂, h₂⟩
      exact ⟨tr₁ ++ tr₂, .seq h₁ h₂⟩
  | choiceLeft _ ih =>
      rcases ih with ⟨tr, htr⟩
      exact ⟨tr, .choiceLeft htr⟩
  | choiceRight _ ih =>
      rcases ih with ⟨tr, htr⟩
      exact ⟨tr, .choiceRight htr⟩
  | iteTrue condition _ ih =>
      rcases ih with ⟨tr, htr⟩
      exact ⟨tr, .iteTrue condition htr⟩
  | iteFalse condition _ ih =>
      rcases ih with ⟨tr, htr⟩
      exact ⟨tr, .iteFalse condition htr⟩
  | whileFalse condition => exact ⟨_, .unit .while (.whileFalse condition)⟩
  | whileTrue condition bodyStep rest _ _ =>
      exact ⟨_, .unit .while (.whileTrue condition bodyStep rest)⟩
  | block atLabel run _ => exact ⟨_, .unit .block (.block atLabel run)⟩
  | next run => exact ⟨_, .unit .next (.next run)⟩

/-- The nonempty trace generated by one or more iterations of a loop. The
terminal `whileFalse` test is deliberately not emitted as a program block. -/
inductive LoopTrace [NextMeaning ι Next]
    (guard : State ι → Bool) (body : Expr ι Next) :
    State ι → State ι → List (Expr ι Next × State ι) → Prop
  | last (condition : guard s = true)
      (bodyTrace : AtomicTrace body s t tr)
      (finished : guard t = false) : LoopTrace guard body s t tr
  | cons (condition : guard s = true)
      (bodyTrace : AtomicTrace body s middle tr₁)
      (rest : LoopTrace guard body middle t tr₂) :
      LoopTrace guard body s t (tr₁ ++ tr₂)

private theorem LoopTrace.exists_of_bigStep_aux
    {ι Next : Type*} {e : Expr ι Next} {s t : State ι}
    [NextMeaning ι Next] (run : BigStep e s t) :
    ∀ {guard : State ι → Bool} {body : Expr ι Next},
      e = .while guard body → guard s = true →
      ∃ tr, LoopTrace guard body s t tr := by
  induction run with
  | skip => simp
  | assign => simp
  | goto => simp
  | seq _ _ _ _ => simp
  | choiceLeft _ _ => simp
  | choiceRight _ _ => simp
  | iteTrue _ _ _ => simp
  | iteFalse _ _ _ => simp
  | block _ _ _ => simp
  | next _ => simp
  | whileFalse conditionFalse =>
      intro guard body heq condition
      cases heq
      simp [condition] at conditionFalse
  | @whileTrue s₀ body₀ middle₀ t₀ guard₀ condition bodyStep rest _ ihRest =>
      intro guard' body' heq condition'
      cases heq
      rcases AtomicTrace.exists_of_bigStep bodyStep with ⟨bodyTr, hbody⟩
      cases hmiddle : guard₀ middle₀ with
      | false =>
          have ht : t₀ = middle₀ := by
            cases rest with
            | whileFalse => rfl
            | whileTrue nextCondition => simp [hmiddle] at nextCondition
          subst t₀
          exact ⟨bodyTr, .last condition' hbody hmiddle⟩
      | true =>
          rcases ihRest rfl hmiddle with ⟨restTr, hrest⟩
          exact ⟨bodyTr ++ restTr, .cons condition' hbody hrest⟩

theorem LoopTrace.exists_of_bigStep
    {ι Next : Type*} {s t : State ι} {body : Expr ι Next}
    [NextMeaning ι Next]
    {guard : State ι → Bool} (condition : guard s = true)
    (run : BigStep (.while guard body) s t) :
    ∃ tr, LoopTrace guard body s t tr :=
  LoopTrace.exists_of_bigStep_aux run rfl condition

/-- A semantic chain in the exact format expected by `SourceLanguage`. -/
inductive SemanticTrace [NextMeaning ι Next] :
    List (Expr ι Next × State ι) → Unit × State ι → Prop
  | last (run : Sem e s final) : SemanticTrace [(e, s)] final
  | cons (run : Sem e s ((), middle))
      (rest : SemanticTrace ((nextExpr, middle) :: tail) final) :
      SemanticTrace ((e, s) :: (nextExpr, middle) :: tail) final

namespace SemanticTrace

theorem nonempty {ι Next : Type*} [NextMeaning ι Next]
    {tr : List (Expr ι Next × State ι)} {final : Unit × State ι}
    (h : SemanticTrace tr final) : tr ≠ [] := by
  cases h <;> simp

theorem chain {ι Next : Type*} [NextMeaning ι Next]
    {tr : List (Expr ι Next × State ι)} {final : Unit × State ι}
    (h : SemanticTrace tr final) :
    tr.IsChain (fun (e₁, s₁) (_, s₂) => ∃ v, Sem e₁ s₁ (v, s₂)) := by
  induction h with
  | last => simp
  | cons run rest ih => exact .cons_cons ⟨(), run⟩ ih

theorem final {ι Next : Type*} [NextMeaning ι Next]
    {tr : List (Expr ι Next × State ι)} {result : Unit × State ι}
    (h : SemanticTrace tr result) :
    match tr.getLast h.nonempty with
    | (e, s) => Sem e s result := by
  induction h with
  | last run => simpa using run
  | cons run rest ih =>
      cases rest with
      | last lastRun => simpa using lastRun
      | cons nextRun tailRun => simpa using ih

private theorem append_aux {ι Next : Type*} [NextMeaning ι Next]
    {tr₁ : List (Expr ι Next × State ι)} {result : Unit × State ι}
    (first : SemanticTrace tr₁ result) :
    ∀ {nextExpr : Expr ι Next} {tail : List (Expr ι Next × State ι)}
      {middle : State ι} {final : Unit × State ι},
      result = ((), middle) →
      SemanticTrace ((nextExpr, middle) :: tail) final →
      SemanticTrace (tr₁ ++ ((nextExpr, middle) :: tail)) final := by
  induction first with
  | last run =>
      intro nextExpr tail middle final hresult second
      rw [hresult] at run
      simpa using SemanticTrace.cons run second
  | cons run rest ih =>
      intro nextExpr tail middle final hresult second
      simpa only [List.cons_append] using
        SemanticTrace.cons run (ih hresult second)

theorem append {ι Next : Type*} [NextMeaning ι Next]
    {tr₁ : List (Expr ι Next × State ι)}
    {nextExpr : Expr ι Next} {tail : List (Expr ι Next × State ι)}
    {middle : State ι} {final : Unit × State ι}
    (first : SemanticTrace tr₁ ((), middle))
    (second : SemanticTrace ((nextExpr, middle) :: tail) final) :
    SemanticTrace (tr₁ ++ ((nextExpr, middle) :: tail)) final :=
  append_aux first rfl second

end SemanticTrace

theorem AtomicTrace.starts
    {ι Next : Type*} {e : Expr ι Next} {s t : State ι}
    {tr : List (Expr ι Next × State ι)} [NextMeaning ι Next]
    (h : AtomicTrace e s t tr) :
    ∃ first rest, tr = (first, s) :: rest := by
  induction h with
  | unit => exact ⟨_, [], rfl⟩
  | seq _ _ ih₁ _ =>
      rcases ih₁ with ⟨first, rest, rfl⟩
      exact ⟨first, _, rfl⟩
  | choiceLeft _ ih => exact ih
  | choiceRight _ ih => exact ih
  | iteTrue _ _ ih => exact ih
  | iteFalse _ _ ih => exact ih

theorem AtomicTrace.toSemanticTrace
    {ι Next : Type*} {e : Expr ι Next} {s t : State ι}
    {tr : List (Expr ι Next × State ι)} [NextMeaning ι Next]
    (h : AtomicTrace e s t tr) :
    SemanticTrace tr ((), t) := by
  induction h with
  | unit _ run => exact .last ⟨rfl, run⟩
  | seq first second ih₁ ih₂ =>
      rcases second.starts with ⟨nextExpr, tail, hshape⟩
      subst hshape
      exact ih₁.append ih₂
  | choiceLeft _ ih => exact ih
  | choiceRight _ ih => exact ih
  | iteTrue _ _ ih => exact ih
  | iteFalse _ _ ih => exact ih

theorem LoopTrace.starts
    {ι Next : Type*} {guard : State ι → Bool} {body : Expr ι Next}
    {s t : State ι} {tr : List (Expr ι Next × State ι)}
    [NextMeaning ι Next] (h : LoopTrace guard body s t tr) :
    ∃ first rest, tr = (first, s) :: rest := by
  induction h with
  | last _ bodyTrace _ => exact bodyTrace.starts
  | cons _ bodyTrace rest _ =>
      rcases bodyTrace.starts with ⟨first, tail, rfl⟩
      exact ⟨first, _, rfl⟩

theorem LoopTrace.toSemanticTrace
    {ι Next : Type*} {guard : State ι → Bool} {body : Expr ι Next}
    {s t : State ι} {tr : List (Expr ι Next × State ι)}
    [NextMeaning ι Next] (h : LoopTrace guard body s t tr) :
    SemanticTrace tr ((), t) := by
  induction h with
  | last _ bodyTrace _ => exact bodyTrace.toSemanticTrace
  | cons _ bodyTrace rest ih =>
      rcases rest.starts with ⟨nextExpr, tail, hshape⟩
      subst hshape
      exact bodyTrace.toSemanticTrace.append ih

private theorem BigStep.while_finished_aux
    {ι Next : Type*} {e : Expr ι Next} {s t : State ι}
    [NextMeaning ι Next] (run : BigStep e s t) :
    ∀ {guard : State ι → Bool} {body : Expr ι Next},
      e = .while guard body → guard t = false := by
  induction run with
  | skip => simp
  | assign => simp
  | goto => simp
  | seq _ _ _ _ => simp
  | choiceLeft _ _ => simp
  | choiceRight _ _ => simp
  | iteTrue _ _ _ => simp
  | iteFalse _ _ _ => simp
  | block _ _ _ => simp
  | next _ => simp
  | whileFalse condition =>
      intro guard body heq
      cases heq
      exact condition
  | whileTrue _ _ _ _ ih =>
      intro guard body heq
      cases heq
      exact ih rfl

theorem BigStep.while_finished
    {ι Next : Type*} {guard : State ι → Bool} {body : Expr ι Next}
    {s t : State ι} [NextMeaning ι Next]
    (run : BigStep (.while guard body) s t) : guard t = false :=
  BigStep.while_finished_aux run rfl

theorem LoopTrace.finished
    {ι Next : Type*} {guard : State ι → Bool} {body : Expr ι Next}
    {s t : State ι} {tr : List (Expr ι Next × State ι)}
    [NextMeaning ι Next]
    (run : LoopTrace guard body s t tr) : guard t = false := by
  induction run with
  | last _ _ finished => exact finished
  | cons _ _ _ ih => exact ih

end Expr

/-- Empty instance-selection tag: it carries no program or PC values. -/
structure GotoLanguage (ι : Type*) (Next : Type*)

abbrev SourceLanguageTag (ι : Type*) := GotoLanguage ι Empty
namespace Expr

def RunningWhole (e : Expr ι Next) (s : State ι) : Prop :=
  ∃ label guard body,
    e = .block label (.while guard body) ∧ guard s = true

def ChosenTrace [NextMeaning ι Next]
    {e : Expr ι Next} {s : State ι} {final : Unit × State ι}
    (_run : Sem e s final) (tr : List (Expr ι Next × State ι)) : Prop :=
  (∃ label guard body,
      e = .block label (.while guard body) ∧
      guard s = true ∧ LoopTrace guard body s final.2 tr) ∨
  (¬ RunningWhole e s ∧ tr = [(e, s)])

@[simp] theorem sem_skip [NextMeaning ι Next] :
    Sem (.skip : Expr ι Next) =
      fun s final => final.1 = () ∧ final.2 = s := by
  funext s final
  apply propext
  constructor
  · rintro ⟨hunit, run⟩
    cases run
    exact ⟨hunit, rfl⟩
  · rintro ⟨hunit, rfl⟩
    exact ⟨hunit, .skip⟩

@[simp] theorem sem_seq [NextMeaning ι Next] (first second : Expr ι Next) :
    Sem (.seq first second) =
      Relation.Comp (null (Sem first)) (Sem second) := by
  funext s final
  apply propext
  constructor
  · rintro ⟨hunit, run⟩
    cases run with
    | seq firstRun secondRun =>
        exact ⟨_, ⟨(), rfl, firstRun⟩, hunit, secondRun⟩
  · rintro ⟨middle, ⟨value, hfirst⟩, hsecond⟩
    cases value
    exact ⟨hsecond.1, .seq hfirst.2 hsecond.2⟩

end Expr

instance gotoSourceLanguage (ι Next : Type*) [NextMeaning ι Next] :
    SourceLanguage (GotoLanguage ι Next) where
  Expr := Expr ι Next
  Val := Unit
  Ctx := State ι
  Sem := Expr.Sem
  Seq := Expr.seq
  SemSeq := Expr.sem_seq
  Skip := Expr.skip
  SemSkip := Expr.sem_skip
  is_trace := Expr.SemanticTrace
  is_trace_chain := Expr.SemanticTrace.chain
  is_trace_not_nil := Expr.SemanticTrace.nonempty
  is_trace_final := Expr.SemanticTrace.final
  trace := Expr.ChosenTrace
  is_trace_trace := by
    intro e s final tr run chosen
    rcases chosen with ⟨label, guard, body, rfl, _, loopTrace⟩ | ⟨_, rfl⟩
    · exact loopTrace.toSemanticTrace
    · exact .last run
  trace_nonempty := by
    intro e s final run
    by_cases whole : Expr.RunningWhole e s
    · rcases whole with ⟨label, guard, body, rfl, condition⟩
      have big := run.2
      cases big with
      | block atLabel loopRun =>
          rcases Expr.LoopTrace.exists_of_bigStep condition loopRun with ⟨tr, loopTrace⟩
          exact ⟨tr, Or.inl ⟨label, guard, body, rfl, condition, loopTrace⟩⟩
    · exact ⟨[(e, s)], Or.inr ⟨whole, rfl⟩⟩

def pcRetract : Retract ι (State ι) where
  emb := fun pc => { store := fun _ => 0, pc := pc }
  extract := State.pc
  emb_extrace := fun _ => rfl

/-! ## Extended monitor state

The source state is not mutated by ghost bookkeeping.  This section gives a
separate monitor command language whose state makes that separation explicit.
-/

structure MonitorState (ι Ghost : Type*) where
  target : State ι
  extension : Ghost

inductive MExpr (ι Ghost : Type*) where
  | skip
  | ghost (update : Ghost → Ghost)
  | seq (first second : MExpr ι Ghost)
  | choice (left right : MExpr ι Ghost)
  | ite (guard : MonitorState ι Ghost → Bool)
      (ifTrue ifFalse : MExpr ι Ghost)
  | while (guard : MonitorState ι Ghost → Bool) (body : MExpr ι Ghost)
  /-- Demonic `next`: the chosen source state is an output of the semantics,
      not an input stored in the syntax. -/
  | next

namespace MExpr

structure Config (ι Ghost : Type*) where
  expr : MExpr ι Ghost
  state : MonitorState ι Ghost

/-- Small-step semantics.  In the `next` rule, every result of the current
    target block is a successor, hence target nondeterminism is demonic. -/
inductive Step (blocks : ι → Expr ι Empty) (pcEnd : ι) :
    Config ι Ghost → Config ι Ghost → Prop
  | ghost : Step blocks pcEnd ⟨.ghost update, s⟩
      ⟨.skip, { s with extension := update s.extension }⟩
  | seqDone : Step blocks pcEnd ⟨.seq .skip second, s⟩ ⟨second, s⟩
  | seqStep (step : Step blocks pcEnd ⟨first, s⟩ ⟨first', t⟩) :
      Step blocks pcEnd ⟨.seq first second, s⟩ ⟨.seq first' second, t⟩
  | choiceLeft : Step blocks pcEnd ⟨.choice left right, s⟩ ⟨left, s⟩
  | choiceRight : Step blocks pcEnd ⟨.choice left right, s⟩ ⟨right, s⟩
  | iteTrue {guard : MonitorState ι Ghost → Bool} {s : MonitorState ι Ghost}
      (condition : guard s = true) :
      Step blocks pcEnd ⟨.ite guard ifTrue ifFalse, s⟩ ⟨ifTrue, s⟩
  | iteFalse {guard : MonitorState ι Ghost → Bool} {s : MonitorState ι Ghost}
      (condition : guard s = false) :
      Step blocks pcEnd ⟨.ite guard ifTrue ifFalse, s⟩ ⟨ifFalse, s⟩
  | while {guard : MonitorState ι Ghost → Bool} {s : MonitorState ι Ghost} :
      Step blocks pcEnd ⟨.while guard body, s⟩
      ⟨.ite guard (.seq body (.while guard body)) .skip, s⟩
  | next {s : MonitorState ι Ghost} {chosen : State ι}
      (notEnd : s.target.pc ≠ pcEnd)
      (run : Expr.BigStep (blocks s.target.pc) s.target chosen) :
      Step blocks pcEnd ⟨.next, s⟩ ⟨.skip, { s with target := chosen }⟩

inductive Final : Config ι Ghost → Prop
  | skip (s : MonitorState ι Ghost) : Final ⟨.skip, s⟩

def Execution (blocks : ι → Expr ι Empty) (pcEnd : ι)
    (e : MExpr ι Ghost) (s t : MonitorState ι Ghost) : Prop :=
  Relation.ReflTransGen (Step blocks pcEnd) ⟨e, s⟩ ⟨.skip, t⟩

/-- Every demonic successor must terminate successfully; the existential
    premise rules out stuck non-final configurations. -/
inductive MustTerminate (blocks : ι → Expr ι Empty) (pcEnd : ι) :
    Config ι Ghost → Prop
  | done (final : Final config) : MustTerminate blocks pcEnd config
  | more (hasStep : ∃ next, Step blocks pcEnd config next)
      (allSteps : ∀ next, Step blocks pcEnd config next → MustTerminate blocks pcEnd next) :
      MustTerminate blocks pcEnd config

theorem Step.target_projection
    {blocks : ι → Expr ι Empty} {pcEnd : ι}
    {before after : Config ι Ghost}
    (step : Step blocks pcEnd before after) :
    before.state.target = after.state.target ∨
      (before.state.target.pc ≠ pcEnd ∧
        Expr.BigStep (blocks before.state.target.pc)
          before.state.target after.state.target) := by
  induction step with
  | ghost => exact .inl rfl
  | seqDone => exact .inl rfl
  | seqStep _ ih => exact ih
  | choiceLeft => exact .inl rfl
  | choiceRight => exact .inl rfl
  | iteTrue => exact .inl rfl
  | iteFalse => exact .inl rfl
  | «while» => exact .inl rfl
  | next notEnd run => exact .inr ⟨notEnd, run⟩

theorem MustTerminate.exists_execution
    {blocks : ι → Expr ι Empty} {pcEnd : ι}
    {config : Config ι Ghost}
    (terminates : MustTerminate blocks pcEnd config) :
    ∃ finalState,
      Relation.ReflTransGen (Step blocks pcEnd) config ⟨.skip, finalState⟩ := by
  induction terminates with
  | done final =>
      cases final with
      | skip s => exact ⟨s, Relation.ReflTransGen.refl⟩
  | more hasStep allSteps ih =>
      rcases hasStep with ⟨next, step⟩
      rcases ih next step with ⟨finalState, rest⟩
      exact ⟨finalState, (Relation.ReflTransGen.single step).trans rest⟩

private theorem steps_target_projection
    {blocks : ι → Expr ι Empty} {pcEnd : ι}
    {before after : Config ι Ghost}
    (run : Relation.ReflTransGen (Step blocks pcEnd) before after) :
    Relation.ReflTransGen
      (fun x y : State ι => x.pc ≠ pcEnd ∧ Expr.BigStep (blocks x.pc) x y)
      before.state.target after.state.target := by
  induction run with
  | refl => exact .refl
  | tail step rest ih =>
      rcases Step.target_projection rest with same | advances
      · simpa [same] using ih
      · exact ih.tail advances

theorem Execution.target_projection
    {blocks : ι → Expr ι Empty} {pcEnd : ι}
    {e : MExpr ι Ghost} {s t : MonitorState ι Ghost}
    (run : Execution blocks pcEnd e s t) :
    Relation.ReflTransGen
      (fun before after : State ι =>
        before.pc ≠ pcEnd ∧ Expr.BigStep (blocks before.pc) before after)
      s.target t.target :=
  steps_target_projection run

theorem blockChain_to_sem
    {blocks : ι → Expr ι Empty} {pcOf : State ι → ι} {pcEnd : ι}
    (pc_agrees : ∀ s, pcOf s = s.pc)
    {start finish : State ι}
    (chain : Relation.ReflTransGen
      (fun before after : State ι =>
        before.pc ≠ pcEnd ∧
        Expr.BigStep (blocks before.pc) before after) start finish) :
    PCBlockChain (s := SourceLanguageTag ι) blocks pcOf pcEnd start finish := by
  induction chain with
  | refl => exact .nil _
  | tail _ step ih =>
      apply ih.append
      exact .cons
        (by simpa [pc_agrees] using step.1)
        ⟨(), rfl, by simpa [pc_agrees] using step.2⟩
        (.nil _)

/-- Demonic total correctness: every branch terminates, and every terminal
    state satisfies the postcondition. -/
def totalTriple {ι Ghost : Type*} (blocks : ι → Expr ι Empty) (pcEnd : ι)
    (e : MExpr ι Ghost)
    (pre : MonitorState ι Ghost → Prop)
    (post : MonitorState ι Ghost → Prop) : Prop :=
  ∀ s, pre s →
    MustTerminate blocks pcEnd ⟨e, s⟩ ∧
    ∀ t, Execution blocks pcEnd e s t → post t

end MExpr

/-! ## Intended demonic ghost-monitor theorem

The result chosen by a nondeterministic target block is an output of `next`.
Consequently the universal branch quantification in `MExpr.totalTriple`
checks every target choice. -/

open SourceLanguage

theorem verification_by_demonic_ghost_monitor
    {target : Expr ι Empty}
        [pcInfo : IsPC ι (s := SourceLanguageTag ι) target]
    {Ghost : Type*}
    {monitor : MExpr ι Ghost}
    {monitorPre monitorPost : MonitorState ι Ghost → Prop}
    (pc_agrees : ∀ s : State ι, pcInfo.pc_retract.extract s = s.pc)
    (source_starts_at_entry : ∀ s, monitorPre s → s.target.pc = pcInfo.pc_start)
    (verified : MExpr.totalTriple
      pcInfo.next_block pcInfo.pc_end monitor monitorPre monitorPost)
    (monitor_finishes_at_exit :
      ∀ s, monitorPost s → s.target.pc = pcInfo.pc_end)
    (monitor_covers_blocks : ∀ initial,
      monitorPre initial →
      ∀ {sourceFinal},
        PCBlockChain (s := SourceLanguageTag ι)
          pcInfo.next_block pcInfo.pc_retract.extract pcInfo.pc_end
          initial.target sourceFinal →
        ∃ monitorFinal,
          MExpr.Execution pcInfo.next_block pcInfo.pc_end
            monitor initial monitorFinal ∧
          monitorFinal.target = sourceFinal)
    :
      SourceLanguage.totalTriple (s := SourceLanguageTag ι) target
        (MonitorState.target '' monitorPre)
        (fun _ => MonitorState.target '' monitorPost) := by
  intro sourceInitial liftedPre
  rcases liftedPre with ⟨monitorInitial, monitorInitialPre, rfl⟩
  constructor
  · intro sourceFinal value sourceRun
    have sourceChain := pcInfo.block_chain_sound sourceRun
    rcases monitor_covers_blocks monitorInitial monitorInitialPre sourceChain with
      ⟨monitorFinal, monitorRun, targetEq⟩
    have monitorFinalPost := (verified monitorInitial monitorInitialPre).2
      monitorFinal monitorRun
    exact ⟨monitorFinal, monitorFinalPost, targetEq⟩
  · rcases verified monitorInitial monitorInitialPre with ⟨terminates, allPost⟩
    rcases terminates.exists_execution with ⟨monitorFinal, monitorRun⟩
    have monitorFinalPost := allPost monitorFinal monitorRun
    have chain := MExpr.Execution.target_projection monitorRun
    have chainSem := MExpr.blockChain_to_sem pc_agrees chain
    rcases pcInfo.block_chain_complete
      (by simpa [pc_agrees] using source_starts_at_entry monitorInitial monitorInitialPre)
      (by simpa [pc_agrees] using monitor_finishes_at_exit monitorFinal monitorFinalPost)
      chainSem with ⟨value, targetRun⟩
    exact ⟨monitorFinal.target, value, targetRun⟩

namespace Example

/-- The type itself enumerates all program-specific control locations. -/
inductive PC where
  | entry
  | double
  | done
  deriving DecidableEq

open Expr

def entryBlock : Expr PC Empty :=
  .block .entry (
    .assign 0 (fun store => store 0 + 1) ;;
    .goto .double)

def doubleBlock : Expr PC Empty :=
  .block .double (
    .assign 0 (fun store => store 0 * 2) ;;
    .goto .done)

def dispatch : Expr PC Empty := .choice entryBlock doubleBlock

/-- The complete goto program is an ordinary expression. -/
def program : Expr PC Empty :=
  .block .entry (.while (fun s => s.pc != .done) dispatch)

/-- This is the function that the future program-specific `IsPC` instance
will install as `next_block`. -/
def nextBlock : PC → Expr PC Empty
  | .entry => entryBlock
  | .double => doubleBlock
  | .done => .block .done .skip

private theorem atomic_dispatch
    (run : AtomicTrace dispatch s t tr) :
    tr = [(nextBlock s.pc, s)] ∧ s.pc ≠ .done := by
  cases run with
  | unit isUnit _ => cases isUnit
  | choiceLeft entryTrace =>
      cases entryTrace with
      | unit _ entryRun =>
          cases entryRun with
          | block atLabel _ =>
              exact ⟨by simp [nextBlock, atLabel], by simp [atLabel]⟩
  | choiceRight doubleTrace =>
      cases doubleTrace with
      | unit _ doubleRun =>
          cases doubleRun with
          | block atLabel _ =>
              exact ⟨by simp [nextBlock, atLabel], by simp [atLabel]⟩

private theorem loop_trace_properties
    (run : LoopTrace (fun s : State PC => s.pc != .done) dispatch s t tr) :
    List.map Prod.fst tr =
        List.map nextBlock (List.map (fun pair => pair.2.pc) tr) ∧
      tr.Forall (fun pair => pair.2.pc ≠ .done) := by
  induction run with
  | last _ bodyTrace _ =>
      rcases atomic_dispatch bodyTrace with ⟨rfl, hpc⟩
      exact ⟨by simp, by simp [hpc]⟩
  | cons _ bodyTrace rest ih =>
      rcases atomic_dispatch bodyTrace with ⟨rfl, hpc⟩
      constructor
      · simpa using ih.1
      · simpa [hpc] using ih.2

instance programIsPC :
    IsPC PC (s := SourceLanguageTag PC) program where
  next_block := nextBlock
  pc_retract := pcRetract
  pc_start := .entry
  pc_end := .done
  start_ne_end := by decide
  trace_determined := by
    intro s final tr run chosen
    rcases chosen with ⟨label, guard, body, heq, condition, loopTrace⟩ | ⟨notWhole, _⟩
    · change (Expr.block .entry (Expr.while (fun s : State PC => s.pc != .done) dispatch)) =
        Expr.block label (Expr.while guard body) at heq
      cases heq
      exact (loop_trace_properties loopTrace).1
    · apply False.elim
      apply notWhole
      exact ⟨.entry, (fun s : State PC => s.pc != .done), dispatch, rfl, by
        have big := run.2
        cases big with
        | block atLabel _ => simp [atLabel]⟩
  trace_start_pc := by
    intro s final tr run _
    have big := run.2
    cases big with
    | block atLabel _ => exact atLabel
  trace_end_pc := by
    intro s final run
    have big := run.2
    cases big with
    | block _ loopRun =>
        have finished := Expr.BigStep.while_finished loopRun
        simpa using finished
  trace_not_end := by
    intro s final tr run chosen
    rcases chosen with ⟨label, guard, body, heq, condition, loopTrace⟩ | ⟨notWhole, _⟩
    · change (Expr.block .entry (Expr.while (fun s : State PC => s.pc != .done) dispatch)) =
        Expr.block label (Expr.while guard body) at heq
      cases heq
      exact (loop_trace_properties loopTrace).2
    · apply False.elim
      apply notWhole
      exact ⟨.entry, (fun s : State PC => s.pc != .done), dispatch, rfl, by
        have big := run.2
        cases big with
        | block atLabel _ => simp [atLabel]⟩
  block_chain_sound := by
    sorry
  block_chain_complete := by
    sorry

end Example

namespace NondeterministicExample

inductive PC where
  | entry
  | left
  | right
  | done
  deriving DecidableEq

open Expr

def entryBlock : Expr PC Empty :=
  .block .entry (.choice (.goto .left) (.goto .right))

def leftBlock : Expr PC Empty :=
  .block .left (.assign 0 (fun _ => 0) ;; .goto .done)

def rightBlock : Expr PC Empty :=
  .block .right (.assign 0 (fun _ => 1) ;; .goto .done)

def dispatch : Expr PC Empty :=
  .choice entryBlock (.choice leftBlock rightBlock)

def program : Expr PC Empty :=
  .block .entry (.while (fun s => s.pc != .done) dispatch)

def nextBlock : PC → Expr PC Empty
  | .entry => entryBlock
  | .left => leftBlock
  | .right => rightBlock
  | .done => .block .done .skip

end NondeterministicExample

end ConcreteGoto
