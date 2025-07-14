import Init.Data.Nat.Basic
import Init.Data.List.Lemmas

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

lemma foldl_mem_of_ne_nil {α : Type*}
    (f : α → α → α)
    (init : α)
    (el : List α)
    (h_ne : el ≠ [])
    (h_f : ∀ acc x, f acc x = acc ∨ f acc x = x) :
    el.foldl f init = init ∨ el.foldl f init ∈ el := by
induction el with
| nil =>
  -- This case is impossible given the hypothesis `h_ne`.
  contradiction
| cons head tail ih =>
  -- The goal is to prove the property for `head :: tail`.
  -- `List.foldl` on `head :: tail` is `(tail.foldl f (f init head))`.
  rw [List.foldl_cons]

  -- The accumulator for the fold over `tail` is now `f init head`.
  -- To proceed, we prove a more general statement that holds for any list and any accumulator.
  have h_general : ∀ (l : List α) (acc : α), l.foldl f acc = acc ∨ l.foldl f acc ∈ l := by
    -- We prove this by a nested induction on the list `l`.
    intro l
    induction l with
    | nil =>
      -- Base case: for an empty list, `foldl` returns the accumulator.
      intro acc
      simp [List.foldl_nil] -- This simplifies to `acc = acc ∨ acc ∈ []`, which is true.
    | cons hd tl ind_hyp =>
      -- Inductive step for our general statement.
      intro acc
      -- Unfold the definition of `foldl` for a non-empty list.
      simp only [List.foldl_cons]
      -- The hypothesis `h_f` states that `f acc hd` is either `acc` or `hd`.
      -- We consider both cases.
      cases h_f acc hd with
      | inl h_acc_eq =>
        -- Case 1: `f acc hd = acc`
        rw [h_acc_eq]
        -- Our goal is now `tl.foldl f acc = acc ∨ tl.foldl f acc ∈ hd :: tl`.
        -- We use the inductive hypothesis on `tl` with accumulator `acc`.
        cases ind_hyp acc with
        | inl h_foldl_eq_acc =>
          -- If `tl.foldl f acc = acc`, the first part of our OR goal is met.
          exact Or.inl h_foldl_eq_acc
        | inr h_foldl_in_tl =>
          -- If `tl.foldl f acc ∈ tl`, it is also in `hd :: tl`.
          exact Or.inr (List.mem_cons_of_mem hd h_foldl_in_tl)
      | inr h_acc_eq_hd =>
        -- Case 2: `f acc hd = hd`
        rw [h_acc_eq_hd]
        -- Our goal is now `tl.foldl f hd = acc ∨ tl.foldl f hd ∈ hd :: tl`.
        -- We use the inductive hypothesis on `tl` with accumulator `hd`.
        cases ind_hyp hd with
        | inl h_foldl_eq_hd =>
          -- If `tl.foldl f hd = hd`, the result is `hd`, which is in `hd :: tl`.
          rw [h_foldl_eq_hd]
          have htmp := @List.mem_concat_self α tl hd
          right
          simp_all
        | inr h_foldl_in_tl =>
          -- If `tl.foldl f hd ∈ tl`, it is also in `hd :: tl`.
          exact Or.inr (List.mem_cons_of_mem hd h_foldl_in_tl)

  -- Now we apply our general statement to the original goal.
  -- The accumulator is `f init head` and the list is `tail`.
  specialize h_general tail (f init head)
  -- `h_general` gives us that the result is either `f init head` or is in `tail`.
  cases h_general with
  | inl h_eq =>
    -- Case A: `tail.foldl f (f init head) = f init head`
    rw [h_eq]
    -- We again use the property of `f` for `f init head`.
    cases h_f init head with
    | inl h_init =>
      -- If `f init head = init`, the result is `init`.
      rw [h_init]
      exact Or.inl rfl
    | inr h_head =>
      -- If `f init head = head`, the result is `head`, which is in `head :: tail`.
      rw [h_head]
      right
      have htmp := @List.mem_concat_self α tail head
      simp_all
  | inr h_mem =>
    -- Case B: `tail.foldl f (f init head) ∈ tail`
    -- If the result is in `tail`, it is also in `head :: tail`.
    exact Or.inr (List.mem_of_mem_tail h_mem)
