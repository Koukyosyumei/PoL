import Init.Data.Nat.Basic
import Init.Data.List.Sublist

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

import PoL.Consensus.Utils
import PoL.Consensus.LongestChain
import PoL.Consensus.ProtocolB.SystemB

lemma living_validator_implies_nonempty_chains
    (sys: SystemB)
    (chains : List Chain)
    (hv: ∃ v ∈ sys.validators, v.crashed = false)
    (hchain : chains = sys.validators.filterMap (fun v ↦ if ¬v.crashed then some v.chain else none)) :
    chains ≠ [] := by {
      -- Assume for contradiction that `chains = []`
      intro hnil
      -- Unpack the existence of a live validator
      rcases hv with ⟨v, hv_in, hv_live⟩
      -- Show `v.chain ∈ chains`
      have hmem : v.chain ∈ chains := by
        -- rewrite `chains` into the filterMap, then discharge the membership
        rw [hchain]
        apply List.mem_filterMap.2
        · -- because `v` is live
          use v
          simp [hv_live]
          exact hv_in
      rw[hnil] at hmem
      simp_all
    }

lemma validator_chain_prefix_of_longest_chain
    (sys : SystemB)
    (v : ValidatorB)
    (chains : List Chain)
    (longest : Chain)
    (hcon : SystemBIsConsistent sys)
    (hmem : v ∈ sys.validators)
    (hcrash : v.crashed = false)
    (hchain : chains = sys.validators.filterMap (fun v ↦ if ¬v.crashed then some v.chain else none))
    (hlongest : longest = get_longest_chain chains) :
    v.chain <+: longest := by {
      rw[hlongest]
      apply longest_chain_is_prefix_of_all_if_consistent
      . apply living_validator_implies_nonempty_chains
        use v
        exact hchain
      . unfold SystemBIsConsistent at hcon
        intro c₁ hc₁ c₂ hc₂
        rw[hchain] at hc₁ hc₂
        obtain ⟨v₁, hv₁_mem, hv₁_eq⟩ := List.mem_filterMap.1 hc₁
        obtain ⟨v₂, hv₂_mem, hv₂_eq⟩ := List.mem_filterMap.1 hc₂
        simp_all
        obtain ⟨hv₁_eq₁, hv₁_eq₂⟩ := hv₁_eq
        obtain ⟨hv₂_eq₁, hv₂_eq₂⟩ := hv₂_eq
        rw[← hv₁_eq₂]
        rw[← hv₂_eq₂]
        exact hcon v₁ hv₁_mem v₂ hv₂_mem hv₁_eq₁ hv₂_eq₁
      simp_all
      use v
    }

lemma system_consistency_unfolded_to_chains
    (sys : SystemB)
    (chains: List Chain)
    (h₁ : SystemBIsConsistent sys)
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
      unfold SystemBIsConsistent at h₁
      apply h₁
      exact hv₁_mem
      exact hv₂_mem
      exact not_crashed₁
      exact not_crashed₂
    }
