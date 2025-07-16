import Init.Data.Nat.Basic
import Init.Data.List.Sublist

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

import PoL.Consensus.Utils
import PoL.Consensus.ProtocolB.SystemB
import PoL.Consensus.LongestChain
import PoL.Consensus.ProtocolB.UtilsB

namespace ProtocolB

/--
A single step of Protocol B.
In view v, the leader collects the chains of the validators, selects the longest chain,
constructs `new_chain` by appending a new block to that chain, and sends `new_chain` to every
non‐crashed validator. The leader is updated in a round-robin fashion.
-/
def protocolB_step_with_crash (sys : SystemB) (new_block: Block) (is_leader_crashed: ℕ → Bool) (next_leader: SystemB → ℕ) : SystemB :=
  -- Step 1. Leader collects chains from non-crashed validators
  let chains := sys.validators.filterMap (λ v ↦ if ¬v.crashed then some v.chain else none)
  -- Step 2. Leader selects the longest chain (assuming non-empty due to h_nonempty and some non-crashed)
  let longest_chain := get_longest_chain chains
  -- Step 3. Leader creates and broadcasts the new chain.
  let new_chain := longest_chain ++ [new_block]
  -- Step 4. Non-crashed validators update their state.
  let new_validators := sys.validators.map (λ v ↦
      if (¬ v.crashed) ∧ (¬ is_leader_crashed v.id) then { chain := new_chain, crashed := v.crashed, id := v.id } else v)
  { validators := new_validators, leader := next_leader sys }

/--
A system protocolB_evolves over `t` time steps, with a new block added at each step.
`protocolB_evolve t` defines the state of the system at time `t`.
-/
def protocolB_evolve
  (initial_sys : SystemB) (blocks : ℕ → Block)
  (is_leader_crashed_at_t: ℕ → ℕ → Bool) (next_leader_at_t: ℕ → SystemB → ℕ)
  : ℕ → SystemB
  | 0   => initial_sys
  | t+1 => protocolB_step_with_crash
            (protocolB_evolve initial_sys blocks is_leader_crashed_at_t next_leader_at_t t)
            (blocks t) (is_leader_crashed_at_t t) (next_leader_at_t t)

theorem protocolB_consistency
    (initial_sys : SystemB)
    (blocks : ℕ → Block)
    (is_leader_crashed_at_t: ℕ → ℕ → Bool)
    (h_initial_consistent : SystemBIsConsistent initial_sys)
    (next_leader_at_t: ℕ → SystemB → ℕ) :
    ∀ t, SystemBIsConsistent (protocolB_evolve initial_sys blocks is_leader_crashed_at_t next_leader_at_t t) := by
  intro t
  induction t with
  | zero =>
    exact h_initial_consistent
  | succ t ih => {
    -- Define the key components from the protocol step.
    let sys_t := protocolB_evolve initial_sys blocks is_leader_crashed_at_t next_leader_at_t t
    let sys_tp1 := protocolB_evolve initial_sys blocks is_leader_crashed_at_t next_leader_at_t (t + 1)
    let new_block := blocks t
    let is_leader_crashed := is_leader_crashed_at_t t
    let old_chains := sys_t.validators.filterMap (fun v ↦ if ¬v.crashed then some v.chain else none)
    let longest_chain := get_longest_chain old_chains
    let new_chain := longest_chain ++ [new_block]
    have h_sys_t : sys_t = (protocolB_evolve initial_sys blocks is_leader_crashed_at_t next_leader_at_t t) := rfl
    have h_sys_tp1 : sys_tp1 = (protocolB_evolve initial_sys blocks is_leader_crashed_at_t next_leader_at_t (t + 1)) := rfl
    have h_old_chains : old_chains = List.filterMap (fun v => if ¬v.crashed then some v.chain else none) sys_t.validators := rfl
    have h_longest_chains : longest_chain = get_longest_chain old_chains := rfl
    have h_new_chain : new_chain = longest_chain ++ [new_block] := rfl
    have h_new_block : new_block = blocks t := rfl

    --unfold protocolB_evolve
    --unfold protocolB_step_with_crash
    intro v₁ hv₁ v₂ hv₂ hnc₁ hnc₂
    rw[← h_sys_tp1] at hv₁ hv₂

    have h_chains_consistent : ∀ c₁ ∈ old_chains, ∀ c₂ ∈ old_chains, ChainsAreConsistent c₁ c₂ := by{
      apply system_consistency_unfolded_to_chains
      exact ih
      rfl
    }
    have h_prefix : ∀ v ∈ sys_tp1.validators, v.crashed = false → v.chain <+: new_chain := by {
      intro v hv
      obtain ⟨v_old, hv_mem, rfl⟩ := List.mem_map.1 hv
      by_cases h₁ : ¬v_old.crashed = true;
      {
        by_cases h₂ : is_leader_crashed_at_t t v_old.id = true;
        {
          rw[← h_sys_t] at hv_mem
          rw[← h_old_chains]
          have htmp : v_old.crashed = false := by {
            simp_all
          }
          rw [← h_sys_t] at ih
          have h_validator_chain_prefix_of_longest_chain := validator_chain_prefix_of_longest_chain sys_t v_old old_chains longest_chain ih hv_mem htmp h_old_chains h_longest_chains
          simp_all
          apply prefix_of_append_singleton
          exact h_validator_chain_prefix_of_longest_chain
        }
        {
          simp_all
        }
      }
      {
        simp_all
      }
    }
    have h_nonupdate : ∀ v ∈ sys_tp1.validators, v.crashed = false → v.chain ≠ new_chain → v.chain ∈ old_chains := by {
      intro v hv hcf hne
      obtain ⟨v_old, hv_mem, rfl⟩ := List.mem_map.1 hv
      have h_crash_v : is_leader_crashed_at_t t v_old.id = true := by {
        by_contra
        rename_i h_id
        simp_all
        by_cases h₁ : ¬v_old.crashed = true;
        {
          simp_all
        }
        {
          simp_all
        }
      }
      rw[h_crash_v]
      by_cases h₁ : ¬v_old.crashed = true;
      {
        simp_all
        rw[← h_sys_t]
        rw[← h_sys_t] at hv_mem
        use v_old
      }
      {
        simp_all
      }
    }

    by_cases h_c₁_new : v₁.chain = new_chain;
    {
      by_cases h_c₂_new : v₂.chain = new_chain;
      {
        unfold ChainsAreConsistent
        left
        rw[h_c₂_new]
        apply h_prefix
        exact hv₁
        simp_all
      }
      {
        unfold ChainsAreConsistent
        right
        rw[h_c₁_new]
        apply h_prefix
        exact hv₂
        unfold Not at hnc₂
        simp at hnc₂
        exact hnc₂
      }
    }
    {
      by_cases h_c₂_new : v₂.chain = new_chain;
      {
        unfold ChainsAreConsistent
        left
        rw[h_c₂_new]
        apply h_prefix
        exact hv₁
        unfold Not at hnc₁
        simp at hnc₁
        exact hnc₁
      }
      {
        apply h_chains_consistent
        . apply h_nonupdate
          exact hv₁
          unfold Not at hnc₁
          simp at hnc₁
          exact hnc₁
          exact h_c₁_new
        . apply h_nonupdate
          exact hv₂
          unfold Not at hnc₂
          simp at hnc₂
          exact hnc₂
          exact h_c₂_new
      }
    }
  }


end ProtocolB
