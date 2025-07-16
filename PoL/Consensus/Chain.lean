import Init.Data.Nat.Basic

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs

/-- A Block is represented as a string (e.g. its hash). -/
abbrev Block := String

/-- A Chain is a list of Blocks. -/
abbrev Chain := List Block

/--
Two chains are consistent if one is a prefix of the other. This ensures
there are no forks among the chains.
-/
def ChainsAreConsistent (c₁ c₂ : Chain) : Prop :=
  c₁ <+: c₂ ∨ c₂ <+: c₁
