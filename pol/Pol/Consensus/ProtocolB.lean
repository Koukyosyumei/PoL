import Init.Data.Nat.Basic

import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

import Pol.Consensus.Utils

namespace ProtocolB

/--
Protocol B update for a single view.
In view v, the leader collects the chains of the validators, selects the longest chain,
constructs `new_chain` by appending a new block to that chain, and sends `new_chain` to every
non‐crashed validator. The leader is updated in a round-robin fashion.
-/
def protocolB_update (sys : System) (new_block: Block) (h_nonempty : sys.validators ≠ []) : System :=
  -- Collect chains from non-crashed validators
  let chains := sys.validators.filterMap (λ v ↦ if ¬v.crashed then some v.chain else none)
  -- Select the longest chain (assuming non-empty due to h_nonempty and some non-crashed)
  let longest_chain := chains.foldl (λ a b ↦ if a.length ≥ b.length then a else b) []
  -- Extend the longest chain with a new block
  let new_chain := longest_chain ++ [new_block]
  { validators := sys.validators.map (λ v ↦
      if ¬ v.crashed then { chain := new_chain, crashed := v.crashed } else v),
    leader := next_leader_round_robin sys h_nonempty }

/--
If the system starts with consistent chains and the new chain is a valid extension of each non‐crashed
validator’s chain, then after the update every non‐crashed validator adopts the same new chain. Hence,
the consistency invariant is maintained.
-/
theorem protocolB_update_preserves_consistency (sys : System) (new_block: Block) (h_consistent : consistent_chains sys) (h_nonempty : sys.validators ≠ []) :
  consistent_chains (protocolB_update sys new_block h_nonempty) := by
  intro i j h_i hj
  have length_eq : (protocolB_update sys new_block h_nonempty).validators.length = sys.validators.length := by
    simp [protocolB_update]
  simp_all [protocolB_update, get_validator]
  split_ifs with h_crashed_i h_crashed_j <;> simp_all

end ProtocolB
