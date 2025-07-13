import Init.Data.Nat.Basic

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

import Pol.Consensus.Utils

namespace ProtocolB

/--
In Protocol B, the leader (assumed to be validator 0 for simplicity) selects
the longest chain from all received chains from non-crashed validators.
-/
def get_longest_chain (chains : List Chain) : Chain :=
  chains.foldl (fun best current ↦ if current.length > best.length then current else best) []

/--
A single step of Protocol B.
In view v, the leader collects the chains of the validators, selects the longest chain,
constructs `new_chain` by appending a new block to that chain, and sends `new_chain` to every
non‐crashed validator. The leader is updated in a round-robin fashion.
-/
def protocolB_step (sys : System) (new_block: Block) (is_leader_crashed: ℕ → Bool) : System :=
  -- Step 1. Leader collects chains from non-crashed validators
  let chains := sys.validators.filterMap (λ v ↦ if ¬v.crashed then some v.chain else none)
  -- Step 2. Leader selects the longest chain (assuming non-empty due to h_nonempty and some non-crashed)
  let longest_chain := get_longest_chain chains
  -- Step 3. Leader creates and broadcasts the new chain.
  let new_chain := longest_chain ++ [new_block]
  -- Step 4. Non-crashed validators update their state.
  let new_validators := sys.validators.map (λ v ↦
      if ¬ v.crashed ∧ (is_leader_crashed v.id) then { chain := new_chain, crashed := v.crashed, id := v.id } else v)
  { validators := new_validators, leader := 0 }

/--
A system evolves over `t` time steps, with a new block added at each step.
`evolve t` defines the state of the system at time `t`.
-/
def evolve (initial_sys : System) (blocks : ℕ → Block) (is_leader_crashed_at_t: ℕ → ℕ → Bool) : ℕ → System
  | 0   => initial_sys
  | t+1 => protocolB_step (evolve initial_sys blocks is_leader_crashed_at_t t) (blocks t) (is_leader_crashed_at_t t)

lemma longestchainincluded
    (chains : List Chain):
    get_longest_chain chains ∈ chains := by
    simp [get_longest_chain]
    sorry

lemma longesteq
    (chains : List Chain) (c L: Chain) (hc: c ∈ chains)
    (h_consistent :
      ∀ c₁ ∈ chains,
      ∀ c₂ ∈ chains,
      ChainsAreConsistent c₁ c₂
    )
    (hL: L = get_longest_chain chains) (hc: L <+: c) :
    L = c := by
    sorry

/--
**Lemma**: If a list of chains is pairwise consistent, the longest chain in
the list is a prefix to all other chains in that list.
-/
lemma longest_chain_is_prefix_of_all
    (chains : List Chain)
    (h_nonempty: chains ≠ [])
    (h_consistent :
      ∀ c₁ ∈ chains,
      ∀ c₂ ∈ chains,
      ChainsAreConsistent c₁ c₂
    ) :
    ∀ c ∈ chains, c <+: get_longest_chain chains := by
  let L := get_longest_chain chains
  intro c hc
  -- Since all chains are consistent, in particular c and L are consistent
  have h_cons : ChainsAreConsistent c L := h_consistent c hc L (by
    exact longestchainincluded chains
  )
  cases h_cons with
  | inl h => exact h
  | inr h =>
    have h₁: L = get_longest_chain chains := rfl
    have h₂ := longesteq chains c L hc h_consistent h₁ h
    rw[← h₂]


theorem protocolB_consistency
    (initial_sys : System)
    (blocks : ℕ → Block)
    (h_initial_consistent : SystemIsConsistent initial_sys) :
    ∀ t, SystemIsConsistent (evolve initial_sys blocks t) := by
  intro t
  induction t with
  | zero =>
    exact h_initial_consistent
  | succ t ih => {
    unfold evolve
    unfold protocolB_step
    simp_all

    let sys_t := evolve initial_sys blocks t
    have h_consistent_t : SystemIsConsistent sys_t := ih
    let sys_next := protocolB_step sys_t (blocks t)
    unfold SystemIsConsistent
    intro v₁_next h_v₁_mem v₂_next h_v₂_mem h_v₁_nc h_v₂_nc
    have : v₁_next.chain = v₂_next.chain := by {
      simp only [evolve, protocolB_step] at h_v₁_mem h_v₂_mem
      simp_all
      sorry
    }
    sorry
  }


end ProtocolB
