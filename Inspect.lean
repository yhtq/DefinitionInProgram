import ITree.Basic
import Paco.PacoDefs

#print ITree.IEq
#check @plfp_init
#check @Lean.Order.lfp_monotone

example {ε ρ} (t₁ t₂ : ITree ε ρ) (h : ITree.IEq t₁ t₂) : True := by
  pinit at h
  rw [@plfp_init (ITree ε ρ → ITree ε ρ → Lean.Order.ReverseImplicationOrder)
    Lean.Order.instCompleteLatticePi] at h
  trivial
