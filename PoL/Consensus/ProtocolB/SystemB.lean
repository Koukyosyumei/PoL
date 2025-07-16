import Init.Data.Nat.Basic

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs

import PoL.Consensus.Chain

/-- A Validator is modeled by its current chain and a flag indicating if it has crashed. -/
structure ValidatorB where
    chain   : List Block
    crashed : Bool
    id      : ℕ
deriving Repr

/-- A System consists of a list of validators and a designated leader (ommitted for simplicity). -/
structure SystemB  where
  validators : List ValidatorB
  leader     : ℕ
deriving Repr

/--
A system has the consistency property if the chains of any two non-crashed
validators are consistent.
-/
def SystemBIsConsistent (sys : SystemB) : Prop :=
  ∀ v₁ ∈ sys.validators,
  ∀ v₂ ∈ sys.validators,
  ¬v₁.crashed → ¬v₂.crashed → ChainsAreConsistent v₁.chain v₂.chain
