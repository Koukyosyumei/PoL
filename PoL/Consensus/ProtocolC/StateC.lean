import Init.Data.Nat.Basic
import Init.Data.List.Sublist
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

import PoL.Consensus.Chain

/-- A chain with its associated view number -/
structure ChainWithView where
  chain : Chain
  view : ℕ
  deriving Repr

structure ValidatorC where
  finalized_chain : Chain      -- Ci: finalized transactions
  known_chain : ChainWithView  -- Ai: known transactions with view number
  crashed : Bool
  id : ℕ
  deriving Repr

structure StateC  where
  validators : List ValidatorC
  leader     : ℕ
deriving Repr

/-- Quorum size (strict majority) -/
def quorum_size (n : ℕ) : ℕ := n / 2 + 1

/-- Check if we have a read quorum -/
def has_read_quorum (received_chains : List ChainWithView) (total_validators : ℕ) : Bool :=
  received_chains.length ≥ quorum_size total_validators

/-- Check if we have a write quorum -/
def has_write_quorum (ack_count : ℕ) (total_validators : ℕ) : Bool :=
  ack_count ≥ quorum_size total_validators

/-- Get the most recently proposed chain (highest view number) -/
def get_most_recent_chain (chains_with_views : List ChainWithView) : Chain :=
  match chains_with_views with
  | [] => []
  | [single] => single.chain
  | _ =>
    let max_view_chain := chains_with_views.foldl
      (fun best current =>
        if current.view > best.view then current
        else if current.view = best.view then
          -- Tiebreaker: use longest chain if same view
          if current.chain.length > best.chain.length then current else best
        else best)
      {chain := [], view := 0}
    max_view_chain.chain
