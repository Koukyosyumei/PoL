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
  induction chains with
  | nil =>
    -- 空リストには要素 c が含まれないので矛盾
    --exact False.elim (List.not_mem_nil _ hc)
    sorry
  | cons d ds ih =>
    -- c ∈ d :: ds から c = d ∨ c ∈ ds が得られる
    cases List.mem_cons.1 hc with
    | inl hd =>
      -- c = d の場合は foldl の結果も d になるので自明
      -- get_longest_chain (d :: ds) = if _ then _ else d = d
      simp_all
      set ds' := d :: ds
      have hd_mem : d ∈ ds' := by {
        unfold ds'
        simp_all
      }
      sorry
    | inr hds =>
      -- c ∈ ds の場合
      simp [get_longest_chain]  -- foldl の定義に沿って if-then-else が展開される
      let L := get_longest_chain ds
      split_ifs with h'
      · -- 分岐1: L.length > d.length のとき、結果は L なので帰納仮定で示せる
        simp_all
        sorry
      · -- 分岐2: ¬(L.length > d.length) ⇒ L.length ≤ d.length で、
        --   d.length ≥ c.length を示せば良い
        have hle : L.length ≤ d.length := by {
          sorry
        }
        have ih' : L.length ≥ c.length := ih hds
        -- L.length ≤ d.length と L.length ≥ c.length から
        -- d.length ≥ c.length が従う
        --exact le_trans hle ih'
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
      if (¬ v.crashed) ∧ (¬ is_leader_crashed v.id) then { chain := new_chain, crashed := v.crashed, id := v.id } else v)
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

lemma prefix_longest
    (sys : System)
    (v : Validator)
    (chains : List Chain)
    (longest : Chain)
    (hmem : v ∈ sys.validators)
    (hcrash : v.crashed = false)
    (hchain : chains = sys.validators.filterMap (fun v ↦ if ¬v.crashed then some v.chain else none))
    (hlongest : longest = get_longest_chain chains) :
    v.chain <+: longest := by {
      sorry
    }

lemma unfold_systemconsistency
    (sys : System)
    (chains: List Chain)
    (h₁ : SystemIsConsistent sys)
    (h₂ : chains = sys.validators.filterMap (fun v ↦ if ¬v.crashed then some v.chain else none)) :
    ∀ c₁ ∈ chains, ∀ c₂ ∈ chains, ChainsAreConsistent c₁ c₂ := by {
      intro c₁ hc₁ c₂ hc₂
      rw [h₂] at hc₁ hc₂
      obtain ⟨v₁, hv₁_mem, hv₁_eq⟩ := List.mem_filterMap.1 hc₁
      obtain ⟨v₂, hv₂_mem, hv₂_eq⟩ := List.mem_filterMap.1 hc₂
      have not_crashed₁ : ¬v₁.crashed := by simp_all
      have rfl_c₁ : v₁.chain = c₁ := by simp_all
      have not_crashed₂ : ¬v₂.crashed := by simp_all
      have rfl_c₂ : v₂.chain = c₂ := by simp_all
      rw[← rfl_c₁, ← rfl_c₂]
      unfold SystemIsConsistent at h₁
      apply h₁
      exact hv₁_mem
      exact hv₂_mem
      exact not_crashed₁
      exact not_crashed₂
    }

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
    -- Define the key components from the protocol step.
    let sys_t := evolve initial_sys blocks is_leader_crashed_at_t t
    let sys_tp1 := evolve initial_sys blocks is_leader_crashed_at_t (t + 1)
    let new_block := blocks t
    let is_leader_crashed := is_leader_crashed_at_t t
    let old_chains := sys_t.validators.filterMap (fun v ↦ if ¬v.crashed then some v.chain else none)
    let longest_chain := get_longest_chain old_chains
    let new_chain := longest_chain ++ [new_block]
    have h_sys_t : sys_t = (evolve initial_sys blocks is_leader_crashed_at_t t) := rfl
    have h_sys_tp1 : sys_tp1 = (evolve initial_sys blocks is_leader_crashed_at_t (t + 1)) := rfl
    have h_old_chains : old_chains = List.filterMap (fun v => if ¬v.crashed then some v.chain else none) sys_t.validators := rfl
    have h_longest_chains : longest_chain = get_longest_chain old_chains := rfl
    have h_new_chain : new_chain = longest_chain ++ [new_block] := rfl
    have h_new_block : new_block = blocks t := rfl

    --unfold evolve
    --unfold protocolB_step
    intro v₁ hv₁ v₂ hv₂ hnc₁ hnc₂
    rw[← h_sys_tp1] at hv₁ hv₂

    have h_chains_consistent : ∀ c₁ ∈ old_chains, ∀ c₂ ∈ old_chains, ChainsAreConsistent c₁ c₂ := by{
      apply unfold_systemconsistency
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
          have h_prefix_longest := prefix_longest sys_t v_old old_chains longest_chain hv_mem htmp h_old_chains h_longest_chains
          simp_all
          apply prefix_of_append_singleton
          exact h_prefix_longest
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
