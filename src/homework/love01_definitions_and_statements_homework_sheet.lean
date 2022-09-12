import ..lectures.love01_definitions_and_statements_demo


/-! # LoVe Homework 1: Definitions and Statements

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (1 point): Fibonacci Numbers

1.1 (1 point). Define the function `fib` that computes the Fibonacci
numbers. -/

def fib : ℕ → ℕ :=
sorry

/-! 1.2 (0 points). Check that your function works as expected. -/

#eval fib 0   -- expected: 0
#eval fib 1   -- expected: 1
#eval fib 2   -- expected: 1
#eval fib 3   -- expected: 2
#eval fib 4   -- expected: 3
#eval fib 5   -- expected: 5
#eval fib 6   -- expected: 8
#eval fib 7   -- expected: 13
#eval fib 8   -- expected: 21


/-! # Question 2 (5 points): Lists - Singletons and Flatten

2.1 (1 point). Define the function `singletons` that turns a list into a list of
singleton lists, where the singleton at each position contains the element in
that position in the original list.

For instance, `singletons [1, 2, 3, 4]` should evaluate to
`[[1], [2], [3], [4]]`.
-/

def singletons {α : Type} : list α → list (list α) :=
sorry

/-! 2.2 (2 points). Define the function `flatten` that takes a list of lists and
"flattens" it into a single list containing all of the elements of the inner
lists.

For example, `flatten [[1], [2, 3], [], [4]]` should evaluate to `[1, 2, 3, 4]`.

You should not call any form of append function (`(++)`, `list.append`, etc.) in
your solution.
-/

def flatten {α : Type} : list (list α) → list α :=
sorry

/-! 2.3 (1 point). State a theorem that says that applying `singletons` and then
    `flatten` to any list gives the same list you started with.
-/

-- Replace `true` with your lemma statement. No need to fill in the `sorry`!
lemma flatten_singletons : true := sorry

/-! 2.4 (1 point). Is it true that applying `flatten` and then `singletons` to a
list gives you back the same list you started with? If so, explain why; if not,
provide an example of a list for which this claim does not hold.
-/

/-
Write your response to part 4 here.
-/


/-! ## Question 3 (5 points): λ-Terms

3.1 (2 points). Complete the following definitions, by replacing the `sorry`
placeholders by terms of the expected type.

Please use reasonable names for the bound variables, e.g., `a : α`, `b : β`,
`c : γ`.

Hint: A procedure for doing so systematically is described in Section 1.1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def B : (α → β) → (γ → α) → γ → β :=
sorry

def S : (α → β → γ) → (α → β) → α → γ :=
sorry

def more_nonsense : (γ → (α → β) → α) → γ → β → α :=
sorry

def even_more_nonsense : (α → α → β) → (β → γ) → α → β → γ :=
sorry

/-! 3.2 (1 point). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Note: Peirce is pronounced like the English word "purse". -/

def weak_peirce : ((((α → β) → α) → α) → β) → β :=
sorry

/-! 3.3 (2 points). Show the typing derivation for your definition of `S` above,
using ASCII or Unicode art. You might find the characters `–` (to draw
horizontal bars) and `⊢` useful.

Feel free to introduce abbreviations to avoid repeating large contexts `C`. -/

-- write your solution here

end LoVe
