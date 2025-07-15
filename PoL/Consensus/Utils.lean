import Init.Data.Nat.Basic
import Init.Data.List.Lemmas

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

lemma foldr_mem_of_ne_nil {α : Type*}
  (f : α → α → α)
  (init : α)
  (el : List α)
  (h_ne : el ≠ [])
  (h_f : ∀ x acc, f x acc = acc ∨ f x acc = x) :
  el.foldr f init = init ∨ el.foldr f init ∈ el := by
induction el with
| nil =>
  -- impossible since `el ≠ []`
  contradiction
| cons x xs ih =>
  -- `el.foldr f init = f x (xs.foldr f init)`
  rw [List.foldr_cons]
  -- we now do a general induction on any list `l` and accumulator `a`
  have h_general : ∀ (l : List α) (a : α), l.foldr f a = a ∨ l.foldr f a ∈ l := by
    intro l
    induction l with
    | nil =>
      intro a
      simp [List.foldr_nil]  -- returns `a = a ∨ a ∈ []`
    | cons y ys IH =>
      intro a
      -- expand `foldr`
      simp only [List.foldr_cons]
      -- by `h_f y a` we know `f y a = a ∨ f y a = y`
      cases h_f y a with
      | inl hy₁ =>
        -- case `f y a = a`

        --rw [hy₁]
        -- apply IH to `ys` with accumulator `a`
        cases IH a with
        | inl h₁  => {
          rw[h₁]
          left
          exact hy₁
        }
        | inr h₂  => {
          cases h_f y ((List.foldr f a ys))
          case cons.inl.inr.inl h₁'
          . right
            rw[h₁']
            apply List.mem_cons_of_mem
            exact h₂
          case cons.inl.inr.inr h₂'
          . right
            rw[h₂']
            exact List.mem_cons_self
        }
      | inr hy₂ =>
        -- case `f y a = y`
        --rw [hy₂]
        -- apply IH to `ys` with accumulator `y`
        cases IH y with
        | inl h₁ =>
          -- `ys.foldr f y = y`, so result is `y ∈ y :: ys`
          cases IH a with
          | inl h₁' => {
            rw[h₁']
            rw[hy₂]
            right
            exact List.mem_cons_self
          }
          | inr h₂' => {
            cases h_f y ((List.foldr f a ys)) with
            | inr h₃' => {
              rw[h₃']
              right
              exact List.mem_cons_self
            }
            | inl h₄' => {
              rw[h₄']
              right
              apply List.mem_cons_of_mem
              exact h₂'
            }
          }
        | inr h₂ =>
          -- `ys.foldr f y ∈ ys`, so also in `y :: ys`
          cases h_f y ((List.foldr f a ys)) with
          | inr h₅' => {
            rw[h₅']
            right
            exact List.mem_cons_self
          }
          | inl h₆' => {
            rw[h₆']
            cases IH a with
            | inl h₇' => {
              left
              exact h₇'
            }
            | inr h₈' => {
              right
              apply List.mem_cons_of_mem
              exact h₈'
            }
          }
  -- now instantiate `l = xs` and `a = init`
  specialize h_general xs init
  cases h_general with
  | inl h_eq =>
    -- `xs.foldr f init = init`, so `foldr` gave `f x init`
    -- but `h_f x init` tells us `f x init = init ∨ f x init = x`
    have : f x init = init ∨ f x init = x := h_f x init
    cases this with
    | inl hx₁ =>
      -- `f x init = init`
      rw [h_eq, hx₁]
      exact Or.inl rfl
    | inr hx₂ =>
      -- `f x init = x`, so result is `x ∈ x :: xs`
      rw [h_eq, hx₂]
      right
      exact List.mem_cons_self
  | inr h_mem =>
    -- `xs.foldr f init ∈ xs`, and `foldr` gave `f x (xs.foldr f init)`,
    -- but that is in `x :: xs` because every `f _ _` result is either its first argument or second,
    -- and both `x` and `xs.foldr f init` lie in `x :: xs`.
    -- We split on `h_f` to show the result is in `x :: xs`.
    right
    cases h_f x (xs.foldr f init) with
    | inl h₁ =>
      -- `f x ... = xs.foldr f init` which ∈ xs, so ∈ cons
      rw[h₁]
      apply List.mem_cons_of_mem
      exact h_mem
    | inr h₂ =>
      rw[h₂]
      exact List.mem_cons_self

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

lemma prefix_of_append_singleton {α : Type*} (x y : List α) (z : α) (h : x <+: y) : x <+: y ++ [z] := by
  -- Unfold the definition of IsPrefix from the hypothesis h
  rcases h with ⟨t, rfl⟩
  -- The goal is to show that there exists a list t' such that y ++ [z] = x ++ t'
  -- By substituting y with x ++ t, we get (x ++ t) ++ [z]
  -- Using the associativity of append, this is equal to x ++ (t ++ [z])
  -- So we can choose t' = t ++ [z]
  use t ++ [z]
  rw [List.append_assoc]

lemma ne_symm {α : Type*} {a b : α} (h : ¬ a = b) : ¬ b = a := by
  intro hba
  apply h
  exact Eq.symm hba
