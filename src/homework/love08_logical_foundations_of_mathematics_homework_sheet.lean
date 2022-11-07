import ..lovelib


/-! # LoVe Homework 8: Logical Foundations of Mathematics

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (9 points): Multisets as a Quotient Type

A multiset (or bag) is a collection of elements that allows for multiple
(but finitely many) occurrences of its elements. For example, the multiset
`{2, 7}` is equal to the multiset `{7, 2}` but different from `{2, 7, 7}`.

Finite multisets can be defined as a quotient over lists. We start with the
type `list α` of finite lists and consider only the number of occurrences of
elements in the lists, ignoring the order in which elements occur. Following
this scheme, `[2, 7, 7]`, `[7, 2, 7]`, and `[7, 7, 2]` would be three equally
valid representations of the multiset `{2, 7, 7}`.

The `list.count` function returns the number of occurrences of an element in a
list. Since it uses equality on elements of type `α`, it requires `α` to belong
to the `decidable_eq` type class. For this reason, the definitions and lemmas
below all take `[decidable_eq α]` as type class argument.

1.1 (1 point). Provide the missing proof below. -/

@[instance] def multiset.rel (α : Type) [decidable_eq α] : setoid (list α) :=
{ r     := λas bs, ∀x, list.count x as = list.count x bs,
  iseqv :=
    sorry }

/-! 1.2 (1 point). Define the type of multisets as the quotient over the
relation `multiset.rel`. -/

def multiset (α : Type) [decidable_eq α] : Type :=
sorry

/-! 1.3 (3 points). Now we have a type `multiset α` but no operations on it.
Basic operations on multisets include the empty multiset (`∅`), the singleton
multiset (`{x} `for any element `x`), and the sum (or union) of two multisets 
(`A ⊎ B` for any multisets `A` and `B`). The sum should be defined so that the 
multiplicities of elements are added; thus, `{2} ⊎ {2, 2} = {2, 2, 2}`.

Fill in the `sorry` placeholders below to implement the basic multiset
operations. -/

def multiset.empty {α : Type} [decidable_eq α] : multiset α :=
sorry

def multiset.singleton {α : Type} [decidable_eq α] (a : α) : multiset α :=
sorry

def multiset.union {α : Type} [decidable_eq α] :
  multiset α → multiset α → multiset α :=
quotient.lift₂
  sorry
  sorry

/-! 1.4 (4 points). Prove that `multiset.union` is commutative and associative,
and has `multiset.empty` as identity element. -/

lemma multiset.union_comm {α : Type} [decidable_eq α] (A B : multiset α) :
  multiset.union A B = multiset.union B A :=
sorry

lemma multiset.union_assoc {α : Type} [decidable_eq α] (A B C : multiset α) :
  multiset.union (multiset.union A B) C =
  multiset.union A (multiset.union B C) :=
sorry

lemma multiset.union_iden_left {α : Type} [decidable_eq α] (A : multiset α) :
  multiset.union multiset.empty A = A :=
sorry

lemma multiset.union_iden_right {α : Type} [decidable_eq α] (A : multiset α) :
  multiset.union A multiset.empty = A :=
sorry


/-! ## Question 2 (4 points + 1 bonus point): Strict Positivity

So far, we've seen a few ways Lean prevents us from breaking the soundness of
its underlying logic: requiring well-founded recursion, using type universes to
avoid Girard's Paradox, and disallowing large elimination from `Prop`. In this
problem, we'll explore another logical "safety feature": *strict positivity* of
inductive definitions.

Strict positivity requires that in any constructor definition for an inductive
type `t`, if any argument to the constructor has a `Π` type (i.e., a
`∀`-quantified type or a function type), then `t` may only appear as the
"result" (i.e., on the right-hand side) in that `Π` type. Such an occurrence of
`t` is known as a *positive* occurrence.

As an example, `legal` obeys strict positivity:

  inductive legal : Type
  | mk : (unit → legal) → legal

But `illegal` does not (this would not compile):

  inductive illegal : Type
  | mk : (illegal → unit) → illegal

In this question, we'll exemplify why Lean must require strict positivity.

**Note**: In order to declare and use the illegal type `self` in this problem,
we must use the `meta` keyword for our declarations, which disables safety
features like positivity checking. Be careful: `meta` disables *many* safety
checks, including well-founded recursion checks. This means that Lean won't
complain if, for instance, you write `meta def uh_oh : false := uh_oh`. However,
when grading your code, we will require that all declarations (besides `self`)
be "safe" Lean declarations -- i.e., if you removed the `meta` keywords and
somehow persuaded Lean to accept `self` as a legal inductive definition, all of
your declarations should compile without errors (in particular, you shouldn't
have any infinite recursion!).

We define `self`, an inductive type that does not obey strict positivity,
below. -/

meta inductive self (α : Type) : Type
| mk : (self → α) → self


/-! 2.1 (1 point). Complete the definition below that produces a value of type
`empty` given a value of type `self empty`. -/

meta def empty_of_self_empty : self empty → empty :=
sorry

/-! 2.2 (2 points). Construct a value of type `self empty` below.

Remember not to accidentally refer to `self_empty` itself in your definition! -/

meta def self_empty : self empty :=
sorry

/-! 2.3 (1 point). Use the preceding declarations to prove `false`.

Hint: recall `empty.elim`. -/

meta def uh_oh : false :=
sorry


/-! 2.4 (1 bonus point). In fact, we can use `self` to define a
*fixpoint combinator*, which allows us to write recursive functions without
relying on Lean's built-in recursive function support (which checks for things
like well-founded recursion). This should immediately raise red flags from a
soundness perspective: if we can write recursive functions without ensuring
well-founded recursion, then we can define functions satisfying, e.g.,
`f 0 = f 0 + 1`, which we have previously shown to enable a proof of `false`.

Formally, a fixpoint combinator is a function `fixp` such that for any function
`f` (if `f` has a fixed point, which we can assume it does), we have
`fixp f = f (fixp f)` (i.e., for all `x`, `fixp f x = f (fixp f) x`).

Below, use `self` to implement a *non-recursive* function `fixp` that behaves as
a fixpoint combinator. To check your work, provide a *non-recursive* function
`fib_nr` such that `fixp fib_nr` is the Fibonacci function. (Remember to make
both of these non-recursive -- otherwise, you're just relying on Lean's built-in
recursion support.)

If you don't have prior familiarity with fixpoint combinators, we recommend you
read the overview below before proceeding. If you are already familiar with the
concept, feel free to skip over the rest of this comment.

--------------------------------------------------------------------------------

Intuitively, a fixpoint combinator allows us to make non-recursive functions
recursive. In order to do so, we define our non-recursive functions with an
extra argument that we treat as a "recursive reference" to our function and use
in our function body wherever we want to make a recursive call. Then, our
fixpoint combinator "fills in" that argument with an actual reference to the
function itself. We'll illustrate how this works by defining the factorial
function using a fixpoint combinator below:

* First, we define a non-recursive function `fact_nr`:

  `def fact_nr : (ℕ → ℕ) → ℕ → ℕ := λ f n, if n = 0 then 1 else f (n - 1)`

  Notice that this function is *not* recursive! Instead, we take an extra
  argument `f` that we treat as though it were a recursive reference to `fact`
  (without the initial function argument). The job of the fixpoint combinator is
  to make this assumption valid!

* Next, supposing we have access to a fixpoint combinator
  
  `fixp : ∀ {α β : Type}, ((α → β) → α → β) → α → β`
  
  (think about why this is the right type!), we define

  `def fact := fixp fact_nr`

  Since this is a partial application, we have `fact : ℕ → ℕ` (you should think
  through the types yourself to verify this). Notice that `fixp` has somehow
  "filled in" the first argument `f` to `fact_nr` -- in particular, since we
  assume `fixp` is correct, it somehow manages to fill in that argument with a
  reference back to `fact` itself.

Recall that we formally defined a fixpoint combinator `fixp` as satisfying
`fixp f = f (fixp f)`. In the above, we said that `fixp fact` is essentially the
result of taking `fact` and "filling in" the first argument with a reference to
an "already-recursive" version of `fact`. So then `fact (fixp fact)` is the
result of calling `fact` with its first argument being an "already-recursive"
version of `fact`. (Why is `fixp fact` "already recursive?" Recall that its
first argument has been filled in with a recursive reference, so any time it
invokes that first argument -- which we treat as a "recursive call" -- it is in
fact recursing!) Thus, `fixp fact = fact (fixp fact)`, so this agrees with our
formal definition! -/

meta def fixp {α β : Type} : ((α → β) → α → β) → (α → β) :=
sorry

meta def fixp_fib : (ℕ → ℕ) → ℕ → ℕ :=
sorry

-- This should compute the Fibonacci sequence (you can use `#eval` to check
-- your work).
meta def fib : ℕ → ℕ := fixp fixp_fib

end LoVe
