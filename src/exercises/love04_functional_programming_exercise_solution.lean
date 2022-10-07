import ..lectures.love03_forward_proofs_demo


/-! # LoVe Exercise 4: Functional Programming -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Reverse of a List

We define a new accumulator-based version of `reverse`. The first argument,
`as`, serves as the accumulator. This definition is __tail-recursive__, meaning
that compilers and interpreters can easily optimize the recursion away,
resulting in more efficient code. -/

def accurev {α : Type} : list α → list α → list α
| as []        := as
| as (x :: xs) := accurev (x :: as) xs

/-! 1.1. Our intention is that `accurev [] xs` should be equal to `reverse xs`.
But if we start an induction, we quickly see that the induction hypothesis is
not strong enough. Start by proving the following generalization (using the
`induction'` tactic or pattern matching): -/

lemma accurev_eq_reverse_append {α : Type} :
  ∀as xs : list α, accurev as xs = reverse xs ++ as
| as []        := by refl
| as (x :: xs) := by simp [reverse, accurev, accurev_eq_reverse_append _ xs]

/-! 1.2. Derive the desired equation. -/

lemma accurev_eq_reverse {α : Type} (xs : list α) :
  accurev [] xs = reverse xs :=
by simp [accurev_eq_reverse_append]

/-! 1.3. Prove the following property.

Hint: A one-line inductionless proof is possible. -/

lemma accurev_accurev {α : Type} (xs : list α) :
  accurev [] (accurev [] xs) = xs :=
by simp [accurev_eq_reverse, reverse_reverse]

/-! 1.4. Prove the following lemma by structural induction, as a "paper" proof.
This is a good exercise to develop a deeper understanding of how structural
induction works.

    lemma accurev_eq_reverse_append {α : Type} :
      ∀as xs : list α, accurev as xs = reverse xs ++ as

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `refl`, `simp`, or `cc` need
not be justified if you think they are obvious (to humans), but you should say
which key lemmas they depend on. You should be explicit whenever you use a
function definition or an introduction rule for an inductive predicate. -/

/-! We perform the proof by structural induction on `xs` (generalizing `as`).

Case `[]`: The goal is `accurev as [] = reverse [] ++ as`. The left-hand side
is `as` by definition of `accurev`. The right-hand side is `as` by definition
of `reverse` and `++`.

Case `x :: xs`: The goal is `accurev as (x :: xs) = reverse (x :: xs) ++ as`.
The induction hypothesis is `∀as, accurev as xs = reverse xs ++ as`.

Let us simplify the goal's left-hand side:

      accurev as (x :: xs)
    = accurev (x :: as) xs        -- by definition of `accurev`
    = reverse xs ++ (x :: as)     -- by the induction hypothesis

Now let us massage the right-hand side so that it matches the simplified
left-hand side:

      reverse (x :: xs) ++ as
    = (reverse xs ++ [x]) ++ as   -- by definition of `reverse`
    = reverse xs ++ ([x] ++ as)   -- by associativity of `++`
    = reverse xs ++ (x :: as)     -- by definition of `++`

The two sides are equal. QED -/


/-! ## Question 2: Drop and Take

The `drop` function removes the first `n` elements from the front of a list. -/

def drop {α : Type} : ℕ → list α → list α
| 0       xs        := xs
| (_ + 1) []        := []
| (m + 1) (x :: xs) := drop m xs

/-! 2.1. Define the `take` function, which returns a list consisting of the the
first `n` elements at the front of a list.

To avoid unpleasant surprises in the proofs, we recommend that you follow the
same recursion pattern as for `drop` above. -/

def take {α : Type} : ℕ → list α → list α
| 0       _         := []
| (_ + 1) []        := []
| (m + 1) (x :: xs) := x :: take m xs

#eval take 0 [3, 7, 11]   -- expected: []
#eval take 1 [3, 7, 11]   -- expected: [3]
#eval take 2 [3, 7, 11]   -- expected: [3, 7]
#eval take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#eval take 4 [3, 7, 11]   -- expected: [3, 7, 11]

#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/-! 2.2. Prove the following lemmas, using `induction'` or pattern matching.
Notice that they are registered as simplification rules thanks to the `@[simp]`
attribute. -/

@[simp] lemma drop_nil {α : Type} :
  ∀n : ℕ, drop n ([] : list α) = []
| 0       := by refl
| (_ + 1) := by refl

@[simp] lemma take_nil {α : Type} :
  ∀n : ℕ, take n ([] : list α) = []
| 0       := by refl
| (_ + 1) := by refl

/-! 2.3. Follow the recursion pattern of `drop` and `take` to prove the
following lemmas. In other words, for each lemma, there should be three cases,
and the third case will need to invoke the induction hypothesis.

Hint: Note that there are three variables in the `drop_drop` lemma (but only two
arguments to `drop`). For the third case, `←add_assoc` might be useful. -/

lemma drop_drop {α : Type} :
  ∀(m n : ℕ) (xs : list α), drop n (drop m xs) = drop (n + m) xs
| 0       n xs        := by refl
| (_ + 1) _ []        := by simp [drop]
| (m + 1) n (x :: xs) :=
  by simp [drop, drop_drop m n xs, ←add_assoc]

lemma take_take {α : Type} :
  ∀(m : ℕ) (xs : list α), take m (take m xs) = take m xs
| 0       _         := by refl
| (_ + 1) []        := by refl
| (m + 1) (x :: xs) := by simp [take, take_take m xs]

lemma take_drop {α : Type} :
  ∀(n : ℕ) (xs : list α), take n xs ++ drop n xs = xs
| 0       _         := by refl
| (_ + 1) []        := by refl
| (m + 1) (x :: xs) := by simp [take, drop, take_drop m]


/-! ## Question 3: A Type of λ-Terms

3.1. Define an inductive type corresponding to the untyped λ-terms, as given
by the following context-free grammar:

    term ::= 'var' string        -- variable (e.g., `x`)
           | 'lam' string term   -- λ-expression (e.g., `λx, t`)
           | 'app' term term     -- application (e.g., `t u`) -/

inductive term : Type
| var : string → term
| lam : string → term → term
| app : term → term → term

/-! 3.2. Register a textual representation of the type `term` as an instance of
the `has_repr` type class. Make sure to supply enough parentheses to guarantee
that the output is unambiguous. -/

def term.repr : term → string
| (term.var s)   := s
| (term.lam s t) := "(λ" ++ s ++ ", " ++ term.repr t ++ ")"
| (term.app t u) := "(" ++ term.repr t ++ " " ++ term.repr u ++ ")"

@[instance] def term.has_repr : has_repr term :=
{ repr := term.repr }

/-! 3.3. Test your textual representation. The following command should print
something like `(λx, ((y x) x))`. -/

#eval (term.lam "x" (term.app (term.app (term.var "y") (term.var "x"))
    (term.var "x")))




/-! ## Question 4: Vectors and Matrices

(Note: this question is long, but good preparation for the last HW problem!)

Recall the type constructor `vec : Type → nat → Type` that represents a sequence
of values of a particular length. -/

inductive vec (α : Type) : ℕ → Type
| nil {}                           : vec 0
| cons (a : α) {n : ℕ} (v : vec n) : vec (n + 1)

-- We define convenience notation for writing vectors. Note that this notation
-- cannot be used when pattern-matching.
local notation `V[]` := vec.nil
local notation `V[` l:(foldr `,` (h t, vec.cons h t) vec.nil) `]` := l

def sample_vector_1 : vec string 0 := V[]
def sample_vector_2 : vec ℕ 4 := V[1, 9, 5, 1]

namespace vec

/-! We can define functions on vectors just as we do on lists and trees. For
instance, here's an `append` function on vectors analogous to its counterpart
for lists: -/

-- NOTE: the length arguments `m` and `n` must go after the colon (i.e., they
-- can't be parameters of `vec_map`). We can then simply ignore those arguments
-- when pattern matching by using `_`, as shown.
def append {α : Type} : ∀ {m n : ℕ}, vec α m → vec α n → vec α (n + m)
| _ _ vec.nil ys := ys
| _ _ (vec.cons x xs) ys := vec.cons x (append xs ys)

/-! 4.1. Implement the function `dot_product` that computes the dot
product of two equal-dimensional (i.e., equal-length in the programmatic sense)
vectors with integer coordinates (i.e., elements). The dot product of two
vectors `V[v₁, v₂, ..., vₙ]` and `V[w₁, w₂, ..., wₙ]` is the number
`v₁ * w₁ + v₂ * w₂ + ... + vₙ * wₙ`, or, more formally, `∑_{i=1}^n (vᵢ * wᵢ)`. -/

def dot_product : ∀ {n : ℕ}, vec ℤ n → vec ℤ n → ℤ
| _ vec.nil vec.nil := 0
| _ (vec.cons m ms) (vec.cons n ns) := m * n + dot_product ms ns



/-! 4.2. We define the *melding* (a coined term) of two equal-length
vectors to be the vector formed by applying a combining function to each
corresponding pair of elements in the two vectors. For instance, the melding of
`V[1, 2, 3]` and `V[4, 5, 6]` using the combining function `(+)` would be the
vector `V[5, 7, 9]`.

Implement a function `meld` that performs this operation. (You'll need to fill
in both the type and body of the function.)
-/

def meld {α β γ : Type} : ∀ {n : ℕ}, (α → β → γ) → vec α n → vec β n → vec γ n
| _ f vec.nil vec.nil := vec.nil
| _ f (vec.cons x xs) (vec.cons y ys) := vec.cons (f x y) (meld f xs ys)

/-! The *product* of two types `α` and `β`, denoted `α × β`, is the type of
pairs `(a, b)` such that `a : α` and `b : β`. (`(a, b)` is syntactic sugar for
`prod.mk a b`, where `prod.mk : ∀ {α β : Type}, α → β → α × β`.) -/

#check (1, 2)
#check prod.mk 1951 "X"

/-! 4.3. The *zipping* of two vectors is the vector formed by pairing
corresponding elements. For instance, zipping `V[1, 2, 3] : vec ℕ 3` and
`["a", "b", "c"] : vec string 3` yields the vector
`[(1, "a"), (2, "b"), (3, "c")] : vec (ℕ × string) 3`.

Use `meld` to implement `zip`. The only modification you may make to the line
below is to replace `sorry` with a *non-recursive* function. -/


def zip {α β : Type} {n : ℕ} : vec α n → vec β n → vec (α × β) n :=
meld prod.mk

/-! 4.4. Prove the lemma below that says that appending and melding
can be done in either order -- that is, that melding the results of appending
two pairs of vectors is the same as appending the result of melding two pairs of
vectors.

You may prove your base case however you wish. However, for the inductive
case, you must use `calc` mode, and you may only use the following terms in your
proof (i.e., as "justifications" after the `:` in `calc` mode):
* `rfl`
* `eq.symm rfl` (this is used for "stepping backward" through functions)
* `by rw [ih]`

You should, of course, fill in the `ih` declaration with the appropriate
variables. -/

lemma meld_append {α β γ : Type} : ∀ {m n : ℕ}
  (f : α → β → γ) (vs : vec α n) (ws : vec β n) (xs : vec α m) (ys : vec β m),
    meld f (append vs xs) (append ws ys) =
    append (meld f vs ws) (meld f xs ys)
| _ _ f vec.nil vec.nil xs ys :=
   by simp [append, meld]
| _ _ f (vec.cons v vs) (vec.cons w ws) xs ys :=
   have ih : _, from meld_append f vs ws xs ys,
calc
  meld f (append (vec.cons v vs) xs) (append (vec.cons w ws) ys)
      = meld f (vec.cons v (append vs xs)) (vec.cons w (append ws ys)) : rfl
  ... = vec.cons (f v w) (meld f (append vs xs) (append ws ys)) : rfl
  ... = vec.cons (f v w) (append (meld f vs ws) (meld f xs ys)) : by rw [ih]
  ... = append (vec.cons (f v w) (meld f vs ws)) (meld f xs ys) : eq.symm rfl


end vec

/-! 4.5. Having defined vectors, we now turn our attention to matrices. An
`r`-by-`c` matrix is a "grid" of numerical entries (we'll use the naturals to
make things simple) with `r` rows and `c` columns. We can think of them as
vectors of vectors: either a length-`c` vector of `r`-element column vectors, or
a length-`r` vector of `c`-element row vectors.

For this problem, we'll use the *row-wise* representation: that is, we'll think
of matrices as a vector containing row vectors.

Fill in the type-level function that defines this type below. That is, `mat r c`
should evaluate to the type whose values are row-wise representations of
matrices that store natural numbers as their entries. -/

def mat (r : ℕ) (c : ℕ) : Type :=
vec (vec ℕ c) r

-- The errors below should disappear if you've defined the type correctly!
#reduce (V[] : mat 0 0)
#reduce (V[V[11, 12], V[21, 22], V[31, 32]] : mat 3 2)
#reduce (V[V[1, 3, 4], V[2, 2, 5]] : mat 2 3)

/-! 4.6. The first type of matrix operation we'll implement is extracting
subcomponents. Below, implement the functions `get_row` and `get_col` that,
respectively, extract a row or column at a specified index from a matrix.

Notice an interesting feature of these functions: they each take as an argument
a *proof* that the requested row or column index is legal for the given matrix.
This allows us to enforce the legality of arguments at the type level.

We provide two helper functions below that you will likely find helpful. (Hint:
notice the second explicit argument to `vec.nth`!) -/

def vec.map {α β : Type} : ∀ {n : ℕ}, (α → β) → vec α n → vec β n
| _ _ vec.nil         := vec.nil
| _ f (vec.cons x xs) := vec.cons (f x) (vec.map f xs)

def vec.nth {α : Type} : ∀ {n : ℕ} (i : ℕ), i < n → vec α n → α
| _ 0       _ (vec.cons x _)  := x
| _ (n + 1) h (vec.cons x xs) := vec.nth n (nat.succ_lt_succ_iff.mp h) xs
| 0 _       h vec.nil         := absurd h dec_trivial

namespace mat

def get_row {r c : ℕ} (i : ℕ) (h : i < r) (m : mat r c) : vec ℕ c :=
vec.nth i h m 

def get_col {r c : ℕ} (i : ℕ) (h : i < c) (m : mat r c) : vec ℕ r :=
vec.map (vec.nth i h) m 


/-! 4.7. Our second matrix operation is addition. Matrix addition proceeds
component-wise: e.g.,
┌     ┐    ┌     ┐     ┌         ┐
| a b |  + | e f |  =  | a+e b+f |
| c d |    | g h |     | c+g d+h |
└     ┘    └     ┘     └         ┘

Below, implement a function `add` for adding two matrices.

Hint: you might find your `vec.zip` function from earlier useful. You also
remain free to use any vector helper functions you might need. -/

def add : ∀ {r c}, mat r c → mat r c → mat r c 
:= λ _ _, vec.meld (vec.meld (+))

end mat

end LoVe
