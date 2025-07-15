import Init.Data.Nat.Basic
import Init.Data.List.Sublist

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

import PoL.Consensus.Utils
import PoL.Consensus.System

/--
In Protocol B, the leader (assumed to be validator 0 for simplicity) selects
the longest chain from all received chains from non-crashed validators.
-/
def get_longest_chain (chains : List Chain) : Chain :=
  chains.foldr (fun current best ↦ if current.length > best.length then current else best) []

lemma get_longest_chain_cons (hd: Chain) (tl: List Chain) :
  get_longest_chain (hd :: tl) =
      if hd.length > (get_longest_chain tl).length then hd else get_longest_chain tl := by
  unfold get_longest_chain
  simp[List.foldr_cons]

lemma length_le_longest_chain_of_mem {chains : List Chain} {c : Chain} (hc : c ∈ chains) :
  (get_longest_chain chains).length ≥ c.length := by
  induction chains
  case nil
  . exact False.elim (List.not_mem_nil hc)
  case cons hd tl ic
  . have hfold : get_longest_chain (hd :: tl) =
      if hd.length > (get_longest_chain tl).length then hd else get_longest_chain tl := get_longest_chain_cons hd tl
    by_cases h_len : hd.length > (get_longest_chain tl).length;
    {
      rw[hfold]
      simp_all
      cases hc
      case pos.inl h
      . rw[h]
      case pos.inr h
      . have htmp := ic h
        exact le_trans htmp (Nat.le_of_lt h_len)
    }
    {
      rw[hfold]
      simp_all
      by_cases h_eq : List.length (get_longest_chain tl) = List.length hd;
      {
        simp_all
        cases hc
        case pos.inl h
        . rw[h]
        case pos.inr h
        . have htmp := ic h
          exact htmp
      }
      {
        have h_lt : List.length hd < List.length (get_longest_chain tl)  := by {
          have h_neq : List.length hd ≠ List.length (get_longest_chain tl) := by {
            simp_all
            exact ne_symm h_eq
          }
          apply lt_of_le_of_ne h_len h_neq
        }
        simp_all
        have h₁ : (if List.length (get_longest_chain tl) < List.length hd then hd else get_longest_chain tl) = (get_longest_chain tl) := by {
          simp_all
        }
        cases hc
        case neg.inl h
        . rw[h]
          rw[h₁]
          exact Nat.le_of_lt h_lt
        case neg.inr h
        . have htmp := ic h
          rw[h₁]
          exact htmp
      }
    }

lemma longest_chain_of_empty_is_empty (chains: List Chain) (he: chains = []):
  get_longest_chain chains = [] := by {
    rw[he]
    simp[get_longest_chain]
  }

lemma longest_chain_mem_or_empty_of_nonempty
    (chains : List Chain):
    get_longest_chain chains = [] ∨
    get_longest_chain chains ∈ chains := by
  by_cases h_ne: chains ≠ [];
  {
    apply foldr_mem_of_ne_nil
    · exact h_ne
    · intro acc x
      by_cases h : x.length < acc.length
      . simp[h]
      . simp[h]
  }
  {
    simp_all
    apply longest_chain_of_empty_is_empty
    rfl
  }

lemma longest_chain_empty_implies_empty_list
  (chains: List Chain)
  (h₁: get_longest_chain chains = [])
  (h₂: get_longest_chain chains ∉ chains) :
  chains = [] := by
  by_contra hc
  cases chains with
  | nil => simp_all
  | cons x xs => {
    simp [get_longest_chain] at h₁ h₂
    by_cases hx : x.length > List.length (get_longest_chain xs);
    {
      simp [get_longest_chain] at hx
      simp [hx] at h₁
      have h : [] ∈ x :: xs := by simp [h₁]
      have : [] ∉ x :: xs := by simp_all

      contradiction
    }
    {
      simp [get_longest_chain] at hx
      have h₃: ¬ List.length
          (List.foldr (fun current best => if List.length best < List.length current then current else best) [] xs) <
        List.length x := by {
          simp_all
        }
      simp [h₃] at h₁ h₂
      rw[h₁] at hx
      simp_all
    }
  }

lemma longest_chain_mem_of_nonempty
  (chains : List Chain)
  (h : chains ≠ []) :
  get_longest_chain chains ∈ chains := by
  -- From `longest_chain_mem_or_empty_of_nonempty`, we have two possibilities for the longest chain.
  have h_cases : get_longest_chain chains = [] ∨ get_longest_chain chains ∈ chains :=
    longest_chain_mem_or_empty_of_nonempty chains

  -- We examine each case.
  cases h_cases with
  | inl h_is_empty =>
    -- Case 1: `get_longest_chain chains = []`.
    -- We show this leads to a contradiction by assuming the opposite of our goal.
    by_contra h_not_in_chains
    -- The lemma `longest_chain_empty_implies_empty_list` takes `h_is_empty` and our new assumption `h_not_in_chains`.
    have h_chains_is_empty : chains = [] := longest_chain_empty_implies_empty_list chains h_is_empty h_not_in_chains
    -- This result contradicts our initial hypothesis `h`.
    exact h h_chains_is_empty
  | inr h_is_in_chains =>
    -- Case 2: `get_longest_chain chains ∈ chains`.
    -- This is our goal, so we are done.
    exact h_is_in_chains

lemma longest_chain_eq_of_prefix_and_mem
    (chains : List Chain) (c L: Chain) (hc_mem: c ∈ chains)
    (hL: L = get_longest_chain chains) (hc: L <+: c) :
    L = c := by
   -- From the definition of get_longest_chain, its length is maximal.
    -- Since `c` is in `chains`, the length of `L` must be >= the length of `c`.
    have h_len_ge : L.length ≥ c.length := by
      rw [hL]
      exact length_le_longest_chain_of_mem hc_mem

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
lemma longest_chain_is_prefix_of_all_if_consistent
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
    exact longest_chain_mem_of_nonempty chains h_nonemoty
  )
  cases h_cons with
  | inl h => exact h
  | inr h =>
    have h₁: L = get_longest_chain chains := rfl
    have h₂ := longest_chain_eq_of_prefix_and_mem chains c L hc h₁ h
    rw[← h₂]

lemma longer_chain_is_left_or_right
  (x acc: Chain):
  (fun current best => if best.length < current.length then current else best) x acc = acc ∨
      (fun current best => if best.length < current.length then current else best) x acc = x := by {
    simp_all
    by_cases h: acc.length < x.length;
    {
      simp_all
    }
    {
      simp_all
    }
  }

lemma living_validator_implies_nonempty_chains
    (sys: System)
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
    (sys : System)
    (v : Validator)
    (chains : List Chain)
    (longest : Chain)
    (hcon : SystemIsConsistent sys)
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
      . unfold SystemIsConsistent at hcon
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
