import ProgramLogicCarte.Wpi
import ProgramLogicCarte.UndefinedBehavior

/-!
# Thread-pool effects

This is the effect and logical handler from `src/threadpool/handler.v`.
`fork` separates the main-thread continuation from the spawned-thread
continuation; `yield` performs an Iris update; `kill` safely terminates the
current thread.  The full-mask variant is exposed separately once the
mask-changing proof-mode rule is available in this port.
-/

namespace ProgramLogicCarte

open Iris Iris.BI Iris.OFE ITree

universe u uρ

inductive Thread : Type u where
  | current
  | spawned
deriving DecidableEq, Repr

inductive ThreadpoolE : Type u → Type u where
  | fork : ThreadpoolE Thread
  | yield : ThreadpoolE (ULift Unit)
  | kill : ThreadpoolE EmptyAnswer

def fork {ε : Type u → Type u} (inject : ThreadpoolE ⟶ ε) : ITree ε Thread :=
  trigger (inject .fork)

def yield {ε : Type u → Type u} (inject : ThreadpoolE ⟶ ε) : ITree ε (ULift Unit) :=
  trigger (inject .yield)

def kill {ε : Type u → Type u} {ρ : Type uρ} (inject : ThreadpoolE ⟶ ε) : ITree ε ρ :=
  vis (inject .kill) fun answer => nomatch answer.down

def spawn {ε : Type u → Type u} (inject : ThreadpoolE ⟶ ε) (child : ITree ε (ULift Unit)) :
    ITree ε (ULift Unit) :=
  ITree.bind (fork inject) fun
  | .current => ret (.up ())
  | .spawned => ITree.bind child fun _ => kill inject

def threadpoolH {GF : BundledGFunctors} [InvGS_gen hlc GF] : IHandler GF ThreadpoolE where
  handle e Φ spawned := match e with
    | .fork => iprop(Φ .current ∗ spawned .spawned)
    | .yield => iprop(|={∅}=> Φ (.up ()))
    | .kill => iprop(|={∅, ⊤}=> True)
  mono e := by
    cases e with
    | fork =>
      intro Φ Φ' spawned spawned'
      change ⊢ iprop(
        (∀ x, Φ x -∗ Φ' x) -∗ □ (∀ x, spawned x -∗ spawned' x) -∗
        (Φ .current ∗ spawned .spawned) -∗ (Φ' .current ∗ spawned' .spawned))
      istart
      iintro HΦ #Hspawn H
      icases H with ⟨Hcurrent, Hchild⟩
      isplitl [HΦ Hcurrent]
      · iapply HΦ $$ Hcurrent
      · iapply Hspawn $$ Hchild
    | yield =>
      intro Φ Φ' spawned spawned'
      change ⊢ iprop(
        (∀ x, Φ x -∗ Φ' x) -∗ □ (∀ x, spawned x -∗ spawned' x) -∗
        (|={∅}=> Φ (.up ())) -∗ |={∅}=> Φ' (.up ()))
      istart
      iintro HΦ _ H
      imod H with H
      imodintro
      iapply HΦ $$ H
    | kill =>
      intro Φ Φ' spawned spawned'
      change ⊢ iprop(
        (∀ x, Φ x -∗ Φ' x) -∗ □ (∀ x, spawned x -∗ spawned' x) -∗
        (|={∅, ⊤}=> True) -∗ |={∅, ⊤}=> True)
      istart
      iintro _ _ H
      iexact H
  ne := by
    intro n α e Φ₁ Φ₂ spawned₁ spawned₂ hΦ hspawned
    cases e with
    | fork => exact BI.sep_ne.ne (hΦ .current) (hspawned .spawned)
    | yield => exact fupd_ne.ne (hΦ (.up ()))
    | kill => exact .rfl

end ProgramLogicCarte
