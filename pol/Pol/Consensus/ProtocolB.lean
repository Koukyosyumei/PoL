import Init.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

namespace ProtocolB

/-- A Block is represented as a string (e.g. its hash). -/
abbrev Block := String

/-- A Chain is a list of Blocks. -/
abbrev Chain := List Block

/-- A Validator is modeled by its current chain and a flag indicating if it has crashed. -/
structure Validator where
    chain : List Block
    crashed : Bool

/-- A System consists of a list of validators and a designated leader (by index). -/
structure System  where
  validators : List Validator
  leader : ℕ

/-- Retrieve the i-th validator (given a proof that i is within bounds). -/
def get_validator (sys : System) (i : ℕ) (h : i < sys.validators.length) : Validator :=
  sys.validators.get ⟨i, h⟩


/-- Two chains are “consistent” if one is a prefix of the other.
    A system has consistent chains if for every pair of non‐crashed validators their chains
    are mutually prefixing (i.e. one extends the other). -/
def consistent_chains (sys : System) : Prop :=
  ∀ i j (h_i : i < sys.validators.length) (h_j : j < sys.validators.length),
    let val_i := get_validator sys i h_i
    let val_j := get_validator sys j h_j
    ¬val_i.crashed → ¬val_j.crashed →
    val_i.chain <+: val_j.chain ∨ val_j.chain <+: val_i.chain

/-- A new chain is a valid extension of an old chain if the old chain is a prefix of the new one. -/
def valid_extension (old_chain new_chain : Chain) : Prop :=
    old_chain <+: new_chain

/--
Round-robin leader selection.
Given a nonempty system, the next leader is chosen by cycling through the validators.
-/
def next_leader (sys : System) (h_nonempty : sys.validators ≠ []) : ℕ :=
    let _ := Nat.ne_of_gt (List.length_pos_of_ne_nil h_nonempty)
    (sys.leader + 1) % sys.validators.length

/--
Protocol B update for a single view.
In view v, the leader collects the chains of the validators, selects the longest chain,
constructs `new_chain` by appending a new block to that chain, and sends `new_chain` to every
non‐crashed validator. The leader is updated in a round-robin fashion.
-/
def protocolB_update (sys : System) (h_nonempty : sys.validators ≠ []) : System :=
  -- Collect chains from non-crashed validators
  let chains := sys.validators.filterMap (λ v ↦ if ¬v.crashed then some v.chain else none)
  -- Select the longest chain (assuming non-empty due to h_nonempty and some non-crashed)
  let longest_chain := chains.foldl (λ a b ↦ if a.length ≥ b.length then a else b) []
  -- Extend the longest chain with a new block (represented as a string)
  let new_chain := longest_chain ++ ["new_block"]
  { validators := sys.validators.map (λ v ↦
      if ¬ v.crashed then { chain := new_chain, crashed := v.crashed } else v),
    leader := next_leader sys h_nonempty }

/--
If the system starts with consistent chains and the new chain is a valid extension of each non‐crashed
validator’s chain, then after the update every non‐crashed validator adopts the same new chain. Hence,
the consistency invariant is maintained.
-/
theorem update_preserves_consistency (sys : System) (h_consistent : consistent_chains sys) (h_nonempty : sys.validators ≠ []) :
  consistent_chains (protocolB_update sys h_nonempty) := by
  intro i j h_i hj
  have length_eq : (protocolB_update sys h_nonempty).validators.length = sys.validators.length := by
    simp [protocolB_update]
  simp_all [protocolB_update, get_validator]
  split_ifs with h_crashed_i h_crashed_j <;> simp_all

end ProtocolB
