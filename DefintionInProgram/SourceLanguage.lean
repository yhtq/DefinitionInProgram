import Mathlib

abbrev null (r : A -> B × A -> Prop) : A -> A -> Prop := fun a1 a2 => ∃ b, r a1 (b, a2)



class SourceLanguage (s : Type*) where
  -- The type of expressions in the source language
  Expr : Type*
  -- The type of values in the source language
  Val : Type*
  [inVal : Inhabited (Val)]
  -- The type of evaluation contexts in the source language
  Ctx : Type*
  -- Non-deterministic evaluation relation for the source language
  Sem : Expr -> (Ctx -> Val × Ctx -> Prop)
  -- `Seq` operation
  Seq : Expr -> Expr -> Expr
  -- Sem of Seq
  SemSeq : ∀ e1 e2 , Sem (Seq e1 e2) = Relation.Comp (null <| Sem e1) (Sem e2)
  Skip : Expr
  SemSkip : Sem Skip = fun ctx => (fun vctx => vctx.1 = Inhabited.default ∧ vctx.2 = ctx)

  /--
    An execution trace: a list of expressions and its initial contexts, with the final result and context.
  -/
  is_trace : List (Expr × Ctx) -> Val × Ctx -> Prop
  is_trace_chain : ∀ {tr ctx}, is_trace tr ctx -> List.IsChain (
    fun (e1, ctx1) (_, ctx2) => ∃ v, Sem e1 ctx1 (v, ctx2)
  ) tr
  is_trace_not_nil : ∀ {tr ctx}, is_trace tr ctx -> tr ≠ []
  is_trace_final : ∀ {tr final}, (h: is_trace tr final) -> match tr.getLast (is_trace_not_nil h) with
    | ⟨e_last, ctx_last_initial⟩ => Sem e_last ctx_last_initial final

  /--
    Any execution of target program has a finite trace. Trace can be non-deterministic.
  -/
  trace : {e : Expr} -> {ctx: Ctx} -> {final : Val × Ctx} -> Sem e ctx final -> List (Expr × Ctx) -> Prop
  is_trace_trace : ∀ {e ctx final tr} {h: Sem e ctx final}, (trace h tr) -> is_trace tr final
  trace_nonempty : ∀ {e ctx final} {h: Sem e ctx final}, ∃ tr, trace h tr

  -- /--
  --   Any execution of target program has a finite trace. Results in a list of passed expressions and its initial contexts.
  --   Trace can be non-deterministic.
  -- -/
  -- trace : (e: Expr) -> (ctx: Ctx) -> (v: Val) -> (ctx': Ctx) -> Sem e ctx (v, ctx') -> List (Expr × Ctx × ι) -> Prop
  -- trace_final_pc : (e: Expr) -> (ctx: Ctx) -> (v: Val) -> (ctx': Ctx) -> Sem e ctx (v, ctx') -> ι -> Prop

  -- /--
  --   Semantic properties of the trace. The trace is a chain of executions.
  -- -/
  -- trace_chain : ∀ e ctx v ctx' h tr,
  --   (trace e ctx v ctx' h tr) -> (List.IsChain (
  --   fun (e1, ctx1, _) (_, ctx2, _) => ∃ v, Sem e1 ctx1 (v, ctx2)
  -- ) tr)
  -- -- /--
  -- --   Properties of `next` in the trace: any execution unit is a part of semantics of `next`
  -- -- -/
  -- -- trace_next : ∀ e ctx v ctx' h, List.IsChain (
  -- --   fun (_, sctx1, pc1) (_, sctx2, pc2)
  -- --     => ∀ vctx1, ∃ v vctx2,
  -- --       Sem next vctx1 (v, vctx2)
  -- --       ∧ ctx_retract.extract vctx1 = sctx1
  -- --       ∧ ctx_retract.extract vctx2 = sctx2
  -- --       ∧ pc_retract.extract vctx1 = pc1
  -- --       ∧ pc_retract.extract vctx2 = pc2
  -- -- ) (trace e ctx v ctx' h)

  -- trace_not_nil : ∀ e ctx v ctx' h tr, (trace e ctx v ctx' h tr) -> tr ≠ []
  -- trace_head : ∀ e ctx v ctx' h tr, (nn: trace e ctx v ctx' h tr) -> (tr.head (trace_not_nil e ctx v ctx' h tr nn)).snd.fst = ctx
  -- trace_last : ∀ e ctx v ctx' h tr, (nn: trace e ctx v ctx' h tr) -> match tr.getLast (trace_not_nil e ctx v ctx' h tr nn) with
  --   | ⟨e_last, ctx_last_initial, _⟩ => Sem e_last ctx_last_initial (v, ctx')
  -- -- trace_next_last : ∀ e ctx v ctx' h, match (trace e ctx v ctx' h).getLast (trace_not_nil e ctx v ctx' h) with
  -- --   | ⟨e_last, ctx_last_initial, pc⟩ => ∀ vctx_last_inital, ∃ vctx_last_final,
  -- --       Sem next vctx_last_inital (value_retract.emb v, vctx_last_final)
  -- --       ∧ ctx_retract.extract vctx_last_inital = ctx_last_initial
  -- --       ∧ pc_retract.extract vctx_last_inital = pc
  -- --       ∧ ctx_retract.extract vctx_last_final = ctx'
  -- --       ∧ pc_retract.extract vctx_last_final = trace_final_pc e ctx v ctx' h

variable {s ι : Type*} [SourceLanguage s]

namespace SourceLanguage

def totalTriple {s : Type*} [SourceLanguage s] (e : Expr s) (p : Ctx s -> Prop) (q : Val s -> Ctx s -> Prop) : Prop :=
  ∀ ctx, p ctx → (∀ ctx' v, Sem e ctx (v, ctx') → q v ctx') ∧ (∃ ctx' v, Sem e ctx (v, ctx'))


/-- The evaluation semantics of a source-language expression. -/
scoped notation "⟦" e "⟧" => SourceLanguage.Sem e

/-- Sequential composition of source-language expressions. -/
scoped infixr:60 " ;; " => SourceLanguage.Seq

/-- Total triple -/
scoped notation:60 "⦃" p "⦄" e "⦃" q "⦄" => SourceLanguage.totalTriple e p q

/--
Uses a total triple to establish the postcondition of a concrete execution.

Registered as an unsafe Aesop rule: after matching a local execution
`Sem e ctx (v, ctx')`, Aesop explores the branch only when it can prove the
corresponding precondition `p ctx`.
-/
@[aesop unsafe 1% apply]
lemma totalTriple_post
    {e : Expr s} {p : Ctx s → Prop} {q : Val s → Ctx s → Prop}
    {ctx ctx' : Ctx s} {v : Val s}
    (h : ⦃ p ⦄ e ⦃ q ⦄) (hp : p ctx) (hsem : Sem e ctx (v, ctx')) : q v ctx' :=
  (h ctx hp).1 ctx' v hsem

@[aesop norm simp]
lemma sem_seq (e1 e2 : Expr s) :
    Sem (e1 ;; e2) = Relation.Comp (null <| Sem e1) (Sem e2) := by
  aesop (add norm 1 simp [SemSeq, Relation.Comp])

/--
Sequential composition of total triples.

The converse is invalid for non-deterministic semantics: a sequence may
terminate through only one possible result of its first component.
-/
@[aesop unsafe 50% apply]
lemma triple_seq (e1 e2 : Expr s )
    (p : Ctx s → Prop) (q : Val s → Ctx s → Prop) :
    (∃ r : Ctx s → Prop, ⦃ p ⦄ e1 ⦃ fun _ => r ⦄ ∧ ⦃ r ⦄ e2 ⦃ q ⦄) →
      ⦃ p ⦄ e1 ;; e2 ⦃ q ⦄ := by
  rintro ⟨r, h₁, h₂⟩ ctx hp
  constructor
  · intro ctx' v hseq
    rw [SemSeq] at hseq
    rcases hseq with ⟨ctx₁, ⟨v₁, h₁sem⟩, h₂sem⟩
    have hr := (h₁ ctx hp).1 ctx₁ v₁ h₁sem
    exact (h₂ ctx₁ hr).1 ctx' v h₂sem
  · rcases (h₁ ctx hp).2 with ⟨ctx₁, v₁, h₁sem⟩
    have hr := (h₁ ctx hp).1 ctx₁ v₁ h₁sem
    rcases (h₂ ctx₁ hr).2 with ⟨ctx₂, v₂, h₂sem⟩
    exact ⟨ctx₂, v₂, by
      rw [SemSeq]
      exact ⟨ctx₁, ⟨⟨v₁, h₁sem⟩, h₂sem⟩⟩⟩


end SourceLanguage

open SourceLanguage

structure Retract (A B : Type*) where
  emb : A → B
  extract : B → A
  emb_extrace : Function.LeftInverse extract emb

def Retract.id (A : Type*) : Retract A A where
  emb := fun x => x
  extract := fun x => x
  emb_extrace := fun _ => rfl

def Retract.comp {A B C : Type*} (r1 : Retract A B) (r2 : Retract B C) : Retract A C where
  emb := r2.emb ∘ r1.emb
  extract := r1.extract ∘ r2.extract
  emb_extrace := by
    intro x
    simp only [Function.comp_apply]
    have h1 := r2.emb_extrace (r1.emb x)
    have h2 := r1.emb_extrace x
    simp only [h1, h2]

@[aesop unsafe 20% apply]
lemma injective_of_retract {A B : Type*} (r : Retract A B) : Function.Injective r.emb := sorry

@[aesop unsafe 20% apply]
lemma surjective_of_retract {A B : Type*} (r : Retract A B) : Function.Surjective r.extract := sorry

/-- A finite execution assembled from the block selected by each current pc.
    The explicit head-recursive form is convenient for synchronizing it with
    a monitor's successive `next` steps. -/
inductive PCBlockChain {s ι : Type*} [SourceLanguage s]
    (nextBlock : ι → Expr s) (pc : Ctx s → ι) (pcEnd : ι) :
    Ctx s → Ctx s → Prop
  | nil (ctx) : PCBlockChain nextBlock pc pcEnd ctx ctx
  | cons {before middle final}
      (notEnd : pc before ≠ pcEnd)
      (step : ∃ value, Sem (nextBlock (pc before)) before (value, middle))
      (rest : PCBlockChain nextBlock pc pcEnd middle final) :
      PCBlockChain nextBlock pc pcEnd before final

theorem PCBlockChain.append
    {s ι : Type*} [SourceLanguage s]
    {nextBlock : ι → Expr s} {pc : Ctx s → ι} {pcEnd : ι}
    {start middle final : Ctx s}
    (first : PCBlockChain nextBlock pc pcEnd start middle)
    (second : PCBlockChain nextBlock pc pcEnd middle final) :
    PCBlockChain nextBlock pc pcEnd start final := by
  induction first with
  | nil => exact second
  | cons notEnd step rest ih => exact .cons notEnd step (ih second)

theorem PCBlockChain.eq_or_cons
    {s ι : Type*} [SourceLanguage s]
    {nextBlock : ι → Expr s} {pc : Ctx s → ι} {pcEnd : ι}
    {start final : Ctx s}
    (chain : PCBlockChain nextBlock pc pcEnd start final) :
    start = final ∨ ∃ middle,
      pc start ≠ pcEnd ∧
      (∃ value, Sem (nextBlock (pc start)) start (value, middle)) ∧
      PCBlockChain nextBlock pc pcEnd middle final := by
  cases chain with
  | nil => exact .inl rfl
  | cons notEnd step rest => exact .inr ⟨_, notEnd, step, rest⟩


/--
  `IsPC` means it is a part of state, and the expression in the trace is uniquely determined by the original pc.
-/
class IsPC (ι : Type*) {s : Type*} [SourceLanguage s] (t : Expr s) where
  next_block : ι → Expr s
  /--
    Context of the source language should contains a pc
  -/
  pc_retract : Retract ι (Ctx s)
  pc_start : ι
  pc_end : ι
  start_ne_end : pc_start ≠ pc_end

  /--
    Expressions in a trace are exactly blocks indicated by pc
  -/
  trace_determined : ∀ {ctx final tr} {h: Sem t ctx final}, (trace h tr) → List.map (fun (e, _) => e) tr = List.map next_block (List.map (fun (_, ctx) => (pc_retract.extract ctx)) tr)

  trace_start_pc : ∀ {ctx final tr} {h: Sem t ctx final}, (trace h tr) → (pc_retract.extract ctx) = pc_start
  trace_end_pc : ∀ {ctx final}, Sem t ctx final -> (pc_retract.extract final.snd) = pc_end
  trace_not_end : ∀ {ctx final tr} {h: Sem t ctx final}, (trace h tr) → (List.Forall  (fun (_, ctx) => (pc_retract.extract ctx ≠ pc_end)) tr)

  block_chain_sound : ∀ {ctx final value}, Sem t ctx (value, final) →
    PCBlockChain next_block pc_retract.extract pc_end ctx final

  /-- Executing the blocks selected successively by `pc`, from `pc_start`
      through `pc_end`, reconstructs an execution of the whole program. -/
  block_chain_complete : ∀ {ctx final},
    pc_retract.extract ctx = pc_start →
    pc_retract.extract final = pc_end →
    PCBlockChain next_block pc_retract.extract pc_end ctx final →
    ∃ value, Sem t ctx (value, final)


variable (ι : Type*)

/-- v is a verification language of target program t with pc ι -/
class VerificationLanguage {s : Type*} (v : Type*) [SourceLanguage s] [SourceLanguage v] (t : Expr s) [IsPC ι t]  where
  ctx_retract : Retract (Ctx s) (Ctx v)
  value_retract : Retract (Val s) (Val v)

  -- /--
  --   Given any execution trace of the target program, there exists a signature `next`
  -- -/
  -- next : {ctx : _} -> {tr : _} -> {final : _} -> (h : Sem t ctx final) -> trace h tr -> Expr v
  -- /--
  --   Expressions other than `next` in the verification language are not allowed to modify the source-language context.
  -- -/
  -- sem_other : ∀ e, ¬(∃ ctx final tr , ∃ (h1 : Sem t ctx final) (h2 : trace h1 tr), e = next h1 h2) → ∀ ctx v ctx', Sem e ctx (v, ctx') → ctx_retract.extract ctx' = ctx_retract.extract ctx

  NextArgs : Type*
  next : NextArgs -> Expr v
  /--
    `next` will fail if the pc of the source-language context is already at the end of the target program.
  -/
  next_pc_end : ∀ ctx args final,
      Sem (next args) ctx final ->
      ((IsPC.pc_retract t).extract (ctx_retract.extract ctx) = (IsPC.pc_end t : ι)) ->
    False

  /--
    Otherwise, semantics of `next` should be a lifting of the semantics of the slice in the target program indicated by the pc.
  -/
  next_sem : ∀ ctx args final,
      Sem (next args) ctx final ->
    let start_pc : ι := (IsPC.pc_retract t).extract (ctx_retract.extract ctx)
    Sem (IsPC.next_block t start_pc) (ctx_retract.extract ctx) ((value_retract.extract final.1, ctx_retract.extract final.2))

  next_sem' : ∀ (pc : ι), ∀ ctx final,
    Sem (IsPC.next_block t pc) ctx final ->
    ∀ args, ∃ ctx_v final_v,
      Sem (next args) ctx_v final_v
      ∧ ctx_retract.extract ctx_v = ctx
      ∧ (Prod.map value_retract.extract ctx_retract.extract) final_v = final
  /--
    Expressions containing not `next`
  -/
  non_next : Expr v -> Prop
  non_next_next : ∀ args, ¬ non_next (next args)
  non_next_seq : ∀ { e1 e2 }, non_next e1 -> non_next e2 -> non_next (Seq e1 e2)
  /--
    Expressions other than `next` in the verification language are not allowed to modify the source-language context.
  -/
  sem_other : ∀ e, non_next e → ∀ ctx v ctx', Sem e ctx (v, ctx') → ctx_retract.extract ctx' = ctx_retract.extract ctx

  /--
    Induction on `next` and non-next
  -/
  next_ind (p : Expr v -> Prop) (hnext : ∀ args, p (next args)) (hnon_next : ∀ e, non_next e -> p e) (hseq : ∀e1 e2, p e1 -> p e2 -> p (Seq e1 e2)) : ∀e, p e



  -- /--
  --   Trace simluation: for any execution of the target program, there exists a trace, which contatins only `next`, which simulates the execution of the target program.
  -- -/
  -- trace_simulation : ∀ (h1 : Sem t ctx final) tr, (h2 : trace h1 tr) -> ∃ vctx_args_tr final_v,
  -- is_trace (List.map (fun vctx => (next args, vctx)) vctx_args_tr) final_v ∧ (Prod.map value_retract.extract ctx_retract.extract) final_v = final ∧ List.map ctx_retract.extract vctx_args_tr = List.map (fun (_, ctx) => ctx) tr

open VerificationLanguage
open IsPC


-- abbrev is_next {s v : Type*} [SourceLanguage s] [SourceLanguage v] (t : Expr s) [VerificationLanguage ι v t] (e : Expr v) : Prop :=
--   ∃ ctx final tr , ∃ (h1 : Sem t ctx final) (h2 : trace h1 tr), e = next ι h1 h2

section Soundness

variable {s v : Type*} [SourceLanguage s] (target : Expr s) [SourceLanguage v] [IsPC ι target] [VerificationLanguage ι v target]

abbrev pc_retract' : Retract ι (Ctx v) := Retract.comp (pc_retract target) (ctx_retract ι target)

/-- An expression that can execute from an end-PC context contains no `next`. -/
private theorem non_next_of_pc_eq_end_exec (e : Expr v) :
    ∀ ctx, (pc_retract' ι target).extract ctx = pc_end target →
      (∃ final, Sem e ctx final) → non_next ι target e := by
  refine next_ind (ι := ι) (t := target) (fun e => ∀ ctx,
    (pc_retract' ι target).extract ctx = pc_end target →
      (∃ final, Sem e ctx final) → non_next ι target e) ?_ ?_ ?_ e
  · intro args ctx hpc ⟨final, hsem⟩
    exact False.elim (next_pc_end (ι := ι) (t := target) ctx args final hsem hpc)
  · intro e hnon _ _ _
    exact hnon
  · intro e1 e2 ih1 ih2 ctx hpc ⟨final, hseq⟩
    rw [SemSeq] at hseq
    rcases hseq with ⟨ctx₁, ⟨v₁, h₁sem⟩, h₂sem⟩
    have hn1 := ih1 ctx hpc ⟨(v₁, ctx₁), h₁sem⟩
    apply non_next_seq (ι := ι) (t := target) hn1
    apply ih2 ctx₁ ?_ ⟨final, h₂sem⟩
    have hkeep := sem_other (ι := ι) (t := target) e1 hn1 ctx v₁ ctx₁ h₁sem
    change (pc_retract target).extract ((ctx_retract ι target).extract ctx) = pc_end target at hpc
    change (pc_retract target).extract ((ctx_retract ι target).extract ctx₁) = pc_end target
    simpa [hkeep] using hpc

theorem non_next_of_pc_eq_end
    {pv : Ctx v -> Prop} {qv : Val v -> Ctx v -> Prop}
    {monitor : Expr v}
    (h : ⦃ pv ⦄ monitor ⦃ qv ⦄)
    (hpv_nonempty : ∃ ctx, pv ctx)
    (hpc_pv : ∀ {ctx}, pv ctx → (pc_retract' ι target).extract ctx = pc_end target)
  : (non_next ι target) monitor := by
  rcases hpv_nonempty with ⟨ctx, hpv⟩
  rcases (h ctx hpv).2 with ⟨ctx', v, hsem⟩
  exact non_next_of_pc_eq_end_exec (ι := ι) (target := target) monitor ctx (hpc_pv hpv)
    ⟨(v, ctx'), hsem⟩

/-
`monitor` is a ghost implementation of `target`: its executions project to
target executions, and every target execution has a lifted monitor execution.
-/
theorem verfication_by_ghost_monitor
    {pv : Ctx v → Prop} {qv : Val v → Ctx v → Prop}
    {monitor : Expr v}
    (h : ⦃ pv ⦄ monitor ⦃ qv ⦄)
    (monitor_refines_target : ∀ {vctx final_v}, pv vctx →
      Sem monitor vctx final_v →
      Sem target ((ctx_retract ι target).extract vctx)
        (Prod.map (value_retract ι target).extract (ctx_retract ι target).extract final_v))
    (target_lifted_by_monitor : ∀ {vctx final}, pv vctx →
      Sem target ((ctx_retract ι target).extract vctx) final →
      ∃ final_v, Sem monitor vctx final_v ∧
        Prod.map (value_retract ι target).extract (ctx_retract ι target).extract final_v = final) :
    ⦃ (ctx_retract ι target).extract '' pv ⦄ target
      ⦃ Function.curry <|
          (Prod.map (value_retract ι target).extract (ctx_retract ι target).extract) ''
            (Function.uncurry qv) ⦄ := by
  rintro _ ⟨vctx, hpv, rfl⟩
  constructor
  · intro ctx' v htarget
    rcases target_lifted_by_monitor hpv htarget with ⟨final_v, hmonitor, hfinal⟩
    exact ⟨final_v, totalTriple_post h hpv hmonitor, hfinal⟩
  · rcases (h vctx hpv).2 with ⟨ctx', v, hmonitor⟩
    exact ⟨(ctx_retract ι target).extract ctx', (value_retract ι target).extract v,
      monitor_refines_target hpv hmonitor⟩

-- theorem verfication_by_ghost_monitor
--     {pv : Ctx v -> Prop} {qv : Val v -> Ctx v -> Prop}
--     {monitor : Expr v}
--     (h : ⦃ pv ⦄ monitor ⦃ qv ⦄)
--     (hpc_pv : ∀ {ctx}, pv ctx → (pc_retract' ι target).extract ctx = pc_start target)
--     (hpc_qv : ∀ {val ctx}, qv val ctx → (pc_retract' ι target).extract ctx = pc_end target)
--   : ⦃ (ctx_retract ι target).extract '' pv ⦄ target ⦃ Function.curry <| (Prod.map (value_retract ι target).extract (ctx_retract ι target).extract) '' (Function.uncurry qv) ⦄ := by sorry

end Soundness
