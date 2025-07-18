import Init.Data.Nat.Basic
import Init.Data.List.Sublist
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

import PoL.Consensus.Chain

structure ValidatorC where
  finalized_chain: Chain
  known_chain: Chain
  crashed: Bool
  id: ℕ
  deriving Repr

structure StateC  where
  validators : List ValidatorC
  leader     : ℕ
deriving Repr

/-- Quorum size (strict majority) -/
def quorum_size (n : ℕ) : ℕ := n / 2 + 1

/-- Check if we have a read quorum -/
def has_read_quorum (received_chains : List Chain) (total_validators : ℕ) : Bool :=
  received_chains.length ≥ quorum_size total_validators

/-- Check if we have a write quorum -/
def has_write_quorum (ack_count : ℕ) (total_validators : ℕ) : Bool :=
  ack_count ≥ quorum_size total_validators
