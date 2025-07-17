import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic

-- Define the matrix type for 2k × 2k Reed-Solomon encoded data
def RSMatrix (k : ℕ) (α : Type*) := Matrix (Fin (2 * k)) (Fin (2 * k)) α

-- Define what it means for a share to be available
def ShareAvailable (k : ℕ) (α : Type*) (M : RSMatrix k α) (i j : Fin (2 * k)) : Prop :=
  ∃ (val : α), M i j = val

-- Define Reed-Solomon recoverability property
def RSRecoverable (k : ℕ) (α : Type*) (shares : Finset (Fin (2 * k)))
  (row_data : Fin (2 * k) → α) : Prop :=
  shares.card ≥ k → ∀ i : Fin (2 * k), ∃ val : α, row_data i = val

-- Define when a row is recoverable
def RowRecoverable (k : ℕ) (α : Type*) (M : RSMatrix k α) (row : Fin (2 * k)) : Prop :=
  ∃ (available_cols : Finset (Fin (2 * k))),
    available_cols.card ≥ k ∧
    ∀ j ∈ available_cols, ShareAvailable k α M row j

-- Define when a column is recoverable
def ColRecoverable (k : ℕ) (α : Type*) (M : RSMatrix k α) (col : Fin (2 * k)) : Prop :=
  ∃ (available_rows : Finset (Fin (2 * k))),
    available_rows.card ≥ k ∧
    ∀ i ∈ available_rows, ShareAvailable k α M i col

-- Define when a specific share is recoverable
def ShareRecoverable (k : ℕ) (α : Type*) (M : RSMatrix k α) (i j : Fin (2 * k)) : Prop :=
  ShareAvailable k α M i j ∨
  RowRecoverable k α M i ∨
  ColRecoverable k α M j
