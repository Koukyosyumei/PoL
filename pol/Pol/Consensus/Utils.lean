import Init.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

/-- A Block is represented as a string (e.g. its hash). -/
abbrev Block := String

/-- A Chain is a list of Blocks. -/
abbrev Chain := List Block

/-- A Validator is modeled by its current chain and a flag indicating if it has crashed. -/
structure Validator where
    chain   : List Block
    crashed : Bool
    id      : ℕ
deriving Repr

/-- A System consists of a list of validators and a designated leader (ommitted for simplicity). -/
structure System  where
  validators : List Validator
  leader     : ℕ
deriving Repr

/--
Two chains are consistent if one is a prefix of the other. This ensures
there are no forks among the chains.
-/
def ChainsAreConsistent (c₁ c₂ : Chain) : Prop :=
  c₁ <+: c₂ ∨ c₂ <+: c₁

/--
A system has the consistency property if the chains of any two non-crashed
validators are consistent.
-/
def SystemIsConsistent (sys : System) : Prop :=
  ∀ v₁ ∈ sys.validators,
  ∀ v₂ ∈ sys.validators,
  ¬v₁.crashed → ¬v₂.crashed → ChainsAreConsistent v₁.chain v₂.chain
