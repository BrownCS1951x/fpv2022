import ..lectures.love01_definitions_and_statements_demo

/-! # LoVe Homework 5: Inductive Predicates

Homework must be done individually. 

This homework combines material from Ch. 5 and part of Ch. 8 of the Hitchhiker's Guide. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (3 points): A Type of λ-Terms

In the Ch 4 lab, we defined the type of untyped lambda terms: -/

inductive term : Type
| var : string → term
| lam : string → term → term
| app : term → term → term

/-!
For instance, this expression represents the term `λ x, λ f, f x`:
-/

#check term.lam "x" (term.lam "f" (term.app (term.var "f") (term.var "x")))

/-! 1.1 (1 point). Define an inductive predicate `is_app` that is `true` if
its argument is of the form `term.app …` and that is false otherwise. -/

-- enter your definition here

/-! 1.2 (2 points). Define an inductive predicate `is_abs_free` that is true if
and only if its argument is a λ-term that contains no λ-expressions.
("abs" stands for "abstraction" here.) -/

-- enter your definition here

/-! ## Question 2 (4 points): Even and Odd

Consider the following inductive definition of even numbers: -/

inductive even : ℕ → Prop
| zero            : even 0
| add_two {n : ℕ} : even n → even (n + 2)

/-! 2.1 (1 point). Define a similar predicate for odd numbers, by completing the
Lean definition below. The definition should distinguish two cases, like `even`,
and should not rely on `even`. -/

inductive odd : ℕ → Prop
-- supply the missing cases here

/-! 2.2 (1 point). Give proof terms for the following propositions, based on
your answer to question 2.1. -/

lemma odd_3 :
  odd 3 :=
sorry

lemma odd_5 :
  odd 5 :=
sorry


/-! 2.3 (1 point). Prove the following lemma in Lean: -/

lemma even_odd {n : ℕ} (heven : even n) :
  odd (n + 1) :=
sorry

/-! 2.4 (1 point). Prove the following lemma in Lean.

Hint: Recall that `¬ a` is defined as `a → false`. -/

lemma even_not_odd {n : ℕ} (heven : even n) :
  ¬ odd n :=
sorry


namespace nodup_lists

/-! ## Question 3 (4 points): Duplicate-Free Sublists

In this problem, we'll use inductive predicates to prove that the sublist of a
list that contains no duplicates also contains no duplicates. (Informally, a
*sublist* of a list `ys` is a list `xs` such that every element of `xs` appears
in the same order in `ys`.)

The predicate `list.sublist : ∀ {α : Type}, list α → list α → Prop`, which
formally specifies the notion of a sublist, is defined as follows:

  inductive sublist : list α → list α → Prop
  | slnil : sublist [] []
  | cons (l₁ l₂ a) : sublist l₁ l₂ → sublist l₁ (a::l₂)
  | cons2 (l₁ l₂ a) : sublist l₁ l₂ → sublist (a::l₁) (a::l₂)

There is also syntactic sugar for the sublist predicate: we can write `xs <+ ys`
instead of `list.sublist xs ys`.

Here are some examples:
* `[] <+ [1, 2, 3]`
* `[2, 3] <+ [2, 3, 4]`
* `[2, 3] <+ [1, 2, 4, 3]`

And here are some non-examples:
* `¬([1] <+ [2, 3])`
* `¬([2, 2] <+ [2, 3])`
* `¬([2, 2, 3, 3] <+ [2, 3, 2, 3])`

We'll also need a couple of additional predicates in order to state the desired
theorem.

3.1 (1 point). Define a predicate `is_in` such that `is_in x xs` holds precisely
when `x` is an element of the list `xs`.

Note: you may not use the equality operator `=` in your solution. -/

-- Fill this in:
inductive is_in {α : Type} : α → list α → Prop
-- ...



-- For the rest of this problem, we'll redefine the `∈` notation to use your
-- `is_in` predicate instead of the default.
local notation (name := list_in_predicate) x ` ∈ ` xs := is_in x xs

/-! 3.2 (1 point). Define a predicate `no_duplicates` such that
`no_duplicates xs` holds precisely when the list `xs` does not contain any
duplicate elements.

Here are some examples:
* `no_duplicates []`
* `no_duplicates [tt]`
* `no_duplicates [2, 1, 3]`

And here are some non-examples:
* `¬(no_duplicates [tt, tt])`
* `¬(no_duplicates [1, 9, 5, 1])`
* `¬(no_duplicates [3, 1, 4, 1, 5])`

Note: you may not use the equality operator `=` in your solution.

Hint: you may find the `is_in` (`∈`) predicate you defined above useful! -/

-- Fill this in:
inductive no_duplicates {α : Type} : list α → Prop
-- ...




/-! 3.3 (2 points). Equipped with these definitions, prove the theorem we stated
at the beginning: the sublist of a duplicate-free list is also duplicate-free.

Hint: choose what to induct on wisely! -/

-- You may find this helper lemma useful when writing your proof.
axiom not_in_of_not_in_sublist {α : Type} {x : α} {xs ys : list α} :
  xs <+ ys → ¬(x ∈ ys) → ¬(x ∈ xs)


theorem no_dups_sublist_of_no_dups {α : Type} (xs ys : list α) :
  no_duplicates ys → xs <+ ys → no_duplicates xs :=
sorry


end nodup_lists




/-! ## Question 4 (2 points): Semantics of the REPEAT Language

We introduce REPEAT, a programming language that resembles the WHILE language
but whose defining feature is a `repeat` loop.

The Lean definition of its abstract syntax tree follows: -/

inductive stmt : Type
| skip   : stmt
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
| unless : (state → Prop) → stmt → stmt
| repeat : ℕ → stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

/-! The `skip`, `assign`, and `S ;; T` statements have the same syntax and
semantics as in the WHILE language.

The `unless b S` statement executes `S` unless `b` is true—i.e., it executes `S`
if `b` is false. Otherwise, `unless b S` does nothing. This construct is
inspired by the Perl language.

The `repeat n S` statement executes `S` exactly `n` times. Thus, `repeat 5 S`
has the same effect as `S ;; S ;; S ;; S ;; S` (as far as the big-step semantics
is concerned), and `repeat 0 S` has the same effect as `skip`.

4.1 (2 points). Complete the following definition of a big-step
semantics: -/

inductive big_step : stmt × state → state → Prop
| skip {s} :
  big_step (stmt.skip, s) s
-- enter the missing cases here

end LoVe
