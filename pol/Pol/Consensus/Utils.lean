import Init.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

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
def next_leader_round_robin (sys : System) (h_nonempty : sys.validators ≠ []) : ℕ :=
    let _ := Nat.ne_of_gt (List.length_pos_of_ne_nil h_nonempty)
    (sys.leader + 1) % sys.validators.length
