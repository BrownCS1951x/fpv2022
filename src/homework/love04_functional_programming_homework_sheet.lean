import ..lectures.love04_functional_programming_demo


/-! # LoVe Homework 4: Functional Programming

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (2 points): Maps

1.1 (1 point). Complete the following definition. The `map_btree` function
should apply its argument `f` to all values of type `α` stored in the tree and
otherwise preserve the tree's structure. -/

def map_btree {α β : Type} (f : α → β) : btree α → btree β :=
sorry

/-! 1.2 (1 point). Prove the following lemma about your `map_btree` function. -/

lemma map_btree_iden {α : Type} :
  ∀t : btree α, map_btree (λa, a) t = t :=
sorry


/-! ## Question 2 (4 points): Tail-Recursive Factorials

Recall the definition of the factorial functions: -/

#check fact

/-! 2.1 (2 points). Experienced functional programmers tend to avoid definitions
such as the above, because they lead to a deep call stack. Tail recursion can be
used to avoid this. Results are accumulated in an argument and returned. This
can be optimized by compilers. For factorials, this gives the following
definition: -/

def accufact : ℕ → ℕ → ℕ
| a 0       := a
| a (n + 1) := accufact ((n + 1) * a) n

/-! Prove that, given 1 as the accumulator `a`, `accufact` computes `fact`.

Hint: You will need to prove a generalized version of the statement as a
separate lemma or `have`, because the desired property fixes `a` to 1, which
yields a too weak induction hypothesis. -/

lemma accufact_1_eq_fact (n : ℕ) :
  accufact 1 n = fact n :=
sorry

/-! 2.2 (2 points). Prove the same property as above again, this time as a
"paper" proof. Follow the guidelines given in question 1.4 of the exercise. -/

-- enter your paper proof here


/-! ## Question 3 (3 points): Gauss's Summation Formula -/

-- `sum_upto f n = f 0 + f 1 + ⋯ + f n`
def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

/-! 3.1 (2 point). Prove the following lemma, discovered by Carl Friedrich Gauss
as a pupil.

Hint: The `mul_add` and `add_mul` lemmas might be useful to reason about
multiplication. -/

#check mul_add
#check add_mul

lemma sum_upto_eq :
  ∀m : ℕ, 2 * sum_upto (λi, i) m = m * (m + 1) :=
sorry

/-! 3.2 (1 point). Prove the following property of `sum_upto`. -/

lemma sum_upto_mul (f g : ℕ → ℕ) :
  ∀n : ℕ, sum_upto (λi, f i + g i) n = sum_upto f n + sum_upto g n :=
sorry




/-! # Question 4: Heterogeneous Lists (6 points)
We've become familiar with `list`s, which contain multiple ordered values of the
same type. But what if we want to store values of different types? Can this be
done in a type-safe way?

Yes! Below we define `hlist`, a type of *heterogeneous lists*. While `list` is
parametrized by a single type (e.g., a `list string` contains `string`s, and a
`list bool` contains `bools`), `hlist` is parametrized by a *list* of types.
Each element of this type-level list defines the type of the entry at the same
position in the `hlist`. For instance, an `hlist [ℕ, string, bool]` contains a
natural number in the first position, a string in the second position, and a
boolean in the third position. Be sure you see how this achieved by the
following inductive definition. -/

inductive hlist : list Type → Type 1
| nil : hlist []
| cons {α : Type} {αs : list Type} : α → hlist αs → hlist (α :: αs)

-- This is notation to let us succinctly write `hlist`s. Note that this notation
-- cannot be used when pattern-matching.
local notation `H[]` := hlist.nil
local notation `H[` l:(foldr `,` (h t, hlist.cons h t) hlist.nil) `]` := l

#check H[]
#check H[9, "hello", tt]
#check H[("value", 4), (λ x, x + 1)]

/-! If we write a function that adds, removes, or changes the types of elements
in an `hlist`, therefore, we must also reflect these changes at the type level.
For instance, consider the function `hlist.snoc` (which appends an element to
the end of an `hlist`) below. Notice the parallel between the type it returns
and the structure of the data it returns! -/

-- Note: for reasons that may become clearer later in this question, the type
-- index variable `αs : list Type` can't go before the colon (i.e., we can't
-- parametrize `snoc` over `αs`). Instead, we take `αs` as an argument to the
-- function and simply "ignore" it when pattern-matching by using an underscore.
def hlist.snoc {α : Type} : ∀ {αs : list Type}, hlist αs → α → hlist (αs ++ [α])
| _ hlist.nil         y := hlist.cons y hlist.nil
| _ (hlist.cons x xs) y := hlist.cons x (hlist.snoc xs y)

#check hlist.snoc H[14, tt] 52
#reduce hlist.snoc H[14, tt] 52

/-! 4.1 (1 point). Write a function `append` that appends two `hlist`s together.
You'll need to complete the type as well as implement the function!

Note: when you're testing a function that returns an `hlist`, you'll need to use
`#reduce` instead of `#eval` (for complicated reasons). Therefore, you'll want
to avoid writing tests using types that are difficult for the kernel to compute
with, such as `string` and `char`. -/

def hlist.append : ∀ {αs βs : list Type}, hlist αs → hlist βs → sorry :=
sorry


/-! Heterogeneous lists can be used in conjunction with traditional lists to
store multi-typed tabular data (similar to Pyret, for those who are familiar).
We can think of some `αs : list Type` as indicating the type stored in each
column and an `hlist αs` as a row. Since every row contains the same types as
the others, a collection of such rows would simply be a list of values of type
`hlist αs`. Therefore, a table, which is a collection of rows, is represented
by a value of type `list (hlist αs)`. For instance, the following table is
represented by a `list (hlist [string, string, nat])`:

------------------------------
| "Providence" | "RI" | 2912 |
| "Pawtucket"  | "RI" | 2860 |
| "Boston"     | "MA" | 2110 |
------------------------------

But we can also think of a table as a collection of columns: each column
contains data of a single type and so is a traditional `list`, but since each
column has a different type, the collection of all the columns must be an
`hlist`. For instance, the column-wise representation of the above would have
type `hlist [list string, list string, list nat]`.

Since these representations are storing equivalent data, it would be useful to
be able to convert between them. This conversion will be our focus for the rest
of this question.

4.2 (1 point). Let `αs : list Type` represent the types stored in a given row of
a table with row-wise representation of type `list (hlist αs)`. Write a function
that produces some `βs : list Type` such that `hlist βs` is the type of the
column-wise representation of that same table. -/

def columnwise_type (αs : list Type) : list Type :=
sorry

/-! 4.3 (2 points). Now that we can state its type, implement the function
`list_hlist_to_hlist_list` that converts the row-wise representation of a table
into a column-wise representation.

Hint: In prior problems, we've simply been ignoring `αs` when pattern-matching.
Here, however, you may find it useful to pattern-match on it! -/

-- You may use these helper functions in your solution
def hlist.hd {α αs} : hlist (α :: αs) → α
| (hlist.cons x _) := x

def hlist.tl {α αs} : hlist (α :: αs) → hlist αs
| (hlist.cons _ xs) := xs

def list_hlist_to_hlist_list :
  ∀ {αs : list Type}, list (hlist αs) → hlist (columnwise_type αs) :=
sorry


/-! But what about the other direction? We might be tempted to declare a
function that turns a collection of columns into a collection of rows. That
function might have this signature: -/

constant hlist_list_to_list_hlist :
  ∀ {αs : list Type}, hlist (columnwise_type αs) → list (hlist αs)

/-! We can describe the type of behavior we expect this function to have. For
instance, if we have a table that consists of a single cell, we'd expect to get
back a table with a single cell: -/
axiom hllh_singleton :
  ∀ (τ : Type) (hl : hlist (columnwise_type [τ])),
    ∃ v : τ, @hlist_list_to_list_hlist [τ] hl = [H[v]]

/- 4.4 (1 point). But, in fact, we cannot define a function with this behavior!
Show that we can obtain `false` using the above declarations. -/

-- Hint: You will likely find `empty.elim` helpful
#check @empty.elim

theorem false_via_hllh : false :=
sorry


/-! 4.5 (1 point). In fact, there is only one function with type
`∀ {αs : list Type}, hlist (αs.map list) → list (hlist αs)`,
and it does not satisfy the property in `hllh_singleton`. Describe this
function's behavior and why it is the only function with this type. Then explain
what we would need to be able to assume about the argument to
`hlist_list_to_list_hlist` in order to create a function that inverts the
row-column representation as we desire. -/

/-
Write your answer to part 7 here.
-/



/-! A final note! This is not the only possible encoding of a heterogeneous
list. Below, we declare a type `hlist'` that stores heterogeneously typed data
but does *not* contain any data about the types it contains at type level. We
also declare a function `hlist'.append` that appends two heterogeneous lists of
this type. -/

inductive hlist'
| nil : hlist'
| cons {α : Type} : α → hlist' → hlist'

def hlist'.append : hlist' → hlist' → hlist'
| hlist'.nil ys := ys
| (hlist'.cons x xs) ys := hlist'.cons x (hlist'.append xs ys)

/-! 

Food for thought: what are some pros and cons of this approach compared to
`hlist`? (How easy is each to declare? To extract data from? How confident
are you that each `append` function is correct by virtue of the fact that it
type-checks?)

We won't be grading your answers here, but if you'd like to share your thoughts,
we're happy to read them!

-/


end LoVe
