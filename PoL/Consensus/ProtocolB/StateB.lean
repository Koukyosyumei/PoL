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

/-- A state consists of a list of validators and a designated leader (ommitted for simplicity). -/
structure StateB  where
  validators : List ValidatorB
  leader     : ℕ
deriving Repr

/--
A state has the consistency property if the chains of any two non-crashed
validators are consistent.
-/
def StateBIsConsistent (state : StateB) : Prop :=
  ∀ v₁ ∈ state.validators,
  ∀ v₂ ∈ state.validators,
  ¬v₁.crashed → ¬v₂.crashed → ChainsAreConsistent v₁.chain v₂.chain
