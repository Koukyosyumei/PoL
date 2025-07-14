import Init.Data.Nat.Basic
import Init.Data.List.Sublist

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

lemma get_longest_chain_length_ge_of_mem {chains : List Chain} {c : Chain} (hc : c ∈ chains) :
  (get_longest_chain chains).length ≥ c.length := by
  sorry

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

lemma foldl_chain_mem_of_ne_nil
    (chains : List Chain)
    (h_ne : chains ≠ []) :
    get_longest_chain chains = [] ∨
    get_longest_chain chains ∈ chains := by
  apply foldl_mem_of_ne_nil
  · exact h_ne
  · intro acc x
    by_cases h : x.length > acc.length
    · simp [h]
    · simp [h]

lemma empty_list_ne
  (chains: List Chain)
  (h₁: get_longest_chain chains = [])
  (h₂: get_longest_chain chains ∉ chains) :
  chains = [] := by
  sorry

lemma longestchainincluded
  (chains : List Chain)
  (h : chains ≠ []) :
  get_longest_chain chains ∈ chains := by
  -- From `foldl_chain_mem_of_ne_nil`, we have two possibilities for the longest chain.
  have h_cases : get_longest_chain chains = [] ∨ get_longest_chain chains ∈ chains :=
    foldl_chain_mem_of_ne_nil chains h

  -- We examine each case.
  cases h_cases with
  | inl h_is_empty =>
    -- Case 1: `get_longest_chain chains = []`.
    -- We show this leads to a contradiction by assuming the opposite of our goal.
    by_contra h_not_in_chains
    -- The lemma `empty_list_ne` takes `h_is_empty` and our new assumption `h_not_in_chains`.
    have h_chains_is_empty : chains = [] := empty_list_ne chains h_is_empty h_not_in_chains
    -- This result contradicts our initial hypothesis `h`.
    exact h h_chains_is_empty
  | inr h_is_in_chains =>
    -- Case 2: `get_longest_chain chains ∈ chains`.
    -- This is our goal, so we are done.
    exact h_is_in_chains

lemma longesteq
    (chains : List Chain) (c L: Chain) (hc_mem: c ∈ chains)
    (hL: L = get_longest_chain chains) (hc: L <+: c) :
    L = c := by
   -- From the definition of get_longest_chain, its length is maximal.
    -- Since `c` is in `chains`, the length of `L` must be >= the length of `c`.
    have h_len_ge : L.length ≥ c.length := by
      rw [hL]
      exact get_longest_chain_length_ge_of_mem hc_mem

    have h_L_c_sublist := List.IsPrefix.sublist hc

    -- From the definition of a prefix, the length of `L` must be <= the length of `c`.
    have h_len_le : L.length ≤ c.length := List.Sublist.length_le h_L_c_sublist

    -- Combining the two length inequalities, the lengths must be equal.
    have h_len_eq : L.length = c.length := Nat.le_antisymm h_len_le h_len_ge

    -- A prefix with the same length as the original list must be equal to that list.
    rw[← List.Sublist.length_eq h_L_c_sublist]
    exact h_len_eq

/--
**Lemma**: If a list of chains is pairwise consistent, the longest chain in
the list is a prefix to all other chains in that list.
-/
lemma longest_chain_is_prefix_of_all
    (chains : List Chain)
    (h_nonemoty : chains ≠ [])
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
    exact longestchainincluded chains h_nonemoty
  )
  cases h_cons with
  | inl h => exact h
  | inr h =>
    have h₁: L = get_longest_chain chains := rfl
    have h₂ := longesteq chains c L hc h₁ h
    rw[← h₂]

theorem protocolB_consistency
    (initial_sys : System)
    (blocks : ℕ → Block)
    (is_leader_crashed_at_t: ℕ → ℕ → Bool)
    (h_initial_consistent : SystemIsConsistent initial_sys) :
    ∀ t, SystemIsConsistent (evolve initial_sys blocks is_leader_crashed_at_t t) := by
  intro t
  induction t with
  | zero =>
    exact h_initial_consistent
  | succ t ih => {
    unfold evolve
    unfold protocolB_step
    simp_all
    sorry
  }


end ProtocolB
