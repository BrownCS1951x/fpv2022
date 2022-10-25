import ..lovelib
import ..lectures.love01_definitions_and_statements_demo
import .love06_hw_support_file


/-! # LoVe Homework 6: Operational and Denotational Semantics

Homework must be done individually.

This homework corresponds to chapters 8 and 10 of the HHG. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

/-! ## Question 1 (4 points): Semantics of the REPEAT Language

We again consider the REPEAT language from the previous homework sheet: -/

inductive stmt : Type
| skip   : stmt
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
| unless : (state → Prop) → stmt → stmt
| repeat : ℕ → stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

/-! Recall the following intuitive description of its semantics:

The `skip`, `assign`, and `S ;; T` statements have the same syntax and
semantics as in the WHILE language.

The `unless b S` statement executes `S` unless `b` is true—i.e., it executes `S`
if `b` is false. Otherwise, `unless b S` does nothing. This construct is
inspired by the Perl language.

The `repeat n S` statement executes `S` exactly `n` times. Thus, `repeat 5 S`
has the same effect as `S ;; S ;; S ;; S ;; S` (as far as the big-step semantics
is concerned), and `repeat 0 S` has the same effect as `skip`.

1.1 (2 points). Complete the following definition of a small-step semantics for
REPEAT: -/

inductive small_step : stmt × state → stmt × state → Prop
| assign {x a s} :
  small_step (stmt.assign x a, s) (stmt.skip, s{x ↦ a s})
-- enter the missing cases here

infixr (name := small_step_hw) ` ⇒ ` := small_step
infixr ` ⇒* ` : 100 := star small_step

/-! 1.2 (1 point). We will now attempt to prove termination of the REPEAT
language. More precisely, we will show that there cannot be infinite chains of
the form

    `(S₀, s₀) ⇒ (S₁, s₁) ⇒ (S₂, s₂) ⇒ ⋯`

Towards this goal, you are asked to define a __measure__ function: a function
`mess` that takes a statement `S` and that returns a natural number indicating
how "big" the statement is. The measure should be defined so that it strictly
decreases with each small-step transition. -/

def mess : stmt → ℕ
| stmt.skip         := 0
-- enter the missing cases here

/-! 1.3 (1 point). Prove that the measure decreases with each small-step
transition. If necessary, revise your answer to question 1.3. -/

lemma small_step_mess_decreases {Ss Tt : stmt × state} (h : Ss ⇒ Tt) :
  mess (prod.fst Ss) > mess (prod.fst Tt) :=
sorry


/-! ## Question 2 (6 points): Denotational Semantics of DOWHILE -/

namespace do_while

/-! Consider the following DOWHILE language: -/

inductive stmt : Type
| skip     : stmt
| assign   : string → (state → ℕ) → stmt
| seq      : stmt → stmt → stmt
| unless   : stmt → (state → Prop) → stmt
| while    : (state → Prop) → stmt → stmt
| do_while : stmt → (state → Prop) → stmt

infixr (name := dowhile_seq) ` ;; ` : 90 := stmt.seq

/-! The `skip`, `assign`, `seq`, and `while` constructs are as for the WHILE
language.

`unless S b` executes `S` if `b` is false in the current state; otherwise, it
does nothing. This statement is inspired by Perl's `unless` conditional.

`do_while S b` first executes `S`. Then, if `b` is true in the resulting state,
it re-enters the loop and executes `S` again, and continues executing `S` until
`b` becomes `false`. The semantics is almost the same as `while b S`, except
that `p` is always executed at least once, even if the condition is not true
initially. This statement is inspired by C's and Java's `do { … } while (…)`
loop.

2.1 (1 point). Give a denotational semantics of DOWHILE.

Hint: Your definition should make it easy to prove lemma `do_while_while` in
question 1.2. -/

def denote : stmt → set (state × state)
| stmt.skip           := Id
| (stmt.assign x a) :=
  {st | prod.snd st = (prod.fst st){x ↦ a (prod.fst st)}}
| (stmt.seq S T)    := denote S ◯ denote T
| (stmt.while b S)    :=
  lfp (λX, ((denote S ◯ X) ⇃ b) ∪ (Id ⇃ (λs, ¬ b s)))
-- enter the missing cases here

notation (name := denote_hw) `⟦` S `⟧`:= denote S

/-! 2.2 (1 point). Prove the following correspondence between `do_while` and
`while`. -/

lemma do_while_while (S : stmt) (b : state → Prop) :
  ⟦stmt.do_while S b⟧ = ⟦S⟧ ◯ ⟦stmt.while b S⟧ :=
sorry

/-! 2.3 (4 points). Prove the following lemmas.

Hint: For all of these, short proofs are possible. It may help, however, to
know what basic expressions such as `p ⇃ (λx, false)` and `p ⇃ (λx, true)` mean.
Make sure to simplify the expressions involving `⇃` before trying to figure out
what to do about `lfp`. -/

lemma lfp_const {α : Type} [complete_lattice α] (a : α) :
  lfp (λX, a) = a :=
sorry

lemma while_false (S : stmt) :
  ⟦stmt.while (λ_, false) S⟧ = Id :=
sorry

lemma comp_Id {α : Type} (r : set (α × α)) :
  r ◯ Id = r :=
sorry

lemma do_while_false (S : stmt) :
  ⟦stmt.do_while S (λ_, false)⟧ = ⟦S⟧ :=
sorry

end do_while

/-! **Note: Everything below this line in this file is entirely optional.**

Since this homework sheet spans three chapters' worth of material, there's a lot
we weren't able to cover in the questions above. So, for those who are
interested and have the time, we provide below two optional questions that
address some interesting extensions of this content.

Question 4 explores another way of viewing fixpoints using iterated function
application. This is a deeper dive into some of the more mathematical topics we
discussed with regard to denotational semantics.

Question 5 explores how we formally represent a functional programming language
with a strong type system. This problem offers a look at some new ideas about,
and properties of, small-step semantics, and it connects to concepts about
typing judgments from the beginning of the semester.

All of these questions are optional, but we encourage you to try some problems
that pique your interest! -/


/-! ## Question 3: Kleene's Theorem

We can compute the fixpoint by iteration by taking the union of all finite
iterations of `f`:

    `lfp f = ⋃i, (f ^^ i) ∅`

where

    `f ^^ i = f ∘ ⋯ ∘ f`

iterates the function `f` `i` times. However, the above characterization of
`lfp` only holds for continuous functions, a concept we will introduce below. -/

def iterate {α : Type} (f : α → α) : ℕ → α → α
| 0       a := a
| (n + 1) a := f (iterate n a)

notation f`^^`n := iterate f n

/-! 3.1. Fill in the missing proofs below.

Hint: Bear in mind that `≤` works on lattices in general, including sets. On
sets, it can be unfolded to `⊆` using `simp [(≤)]`. Moreover, when you see
`h : A ⊆ B` in a goal, you can imagine that you have `?a ∈ A → ?a ∈ B` by
definition, or unfold the definition using `simp [(⊆), set.subset]`. -/

def Union {α : Type} (s : ℕ → set α) : set α :=
{a | ∃n, a ∈ s n}

lemma Union_le {α : Type} {s : ℕ → set α} (A : set α) (h : ∀i, s i ≤ A) :
  Union s ≤ A :=
sorry

/-! A continuous function `f` is a function that commutes with the union of any
monotone sequence `s`: -/

def continuous {α : Type} (f : set α → set α) : Prop :=
∀s : ℕ → set α, monotone s → f (Union s) = Union (λi, f (s i))

/-! We need to prove that each continuous function is monotone. To achieve this,
we will need the following sequence: -/

def bi_seq {α : Type} (A B : set α) : ℕ → set α
| 0       := A
| (n + 1) := B

/-! For example, `bi_seq A B` is the sequence A, B, B, B, …. -/

lemma monotone_bi_seq {α : Type} (A B : set α) (h : A ≤ B) :
  monotone (bi_seq A B)
| 0       0       _ := le_refl _
| 0       (n + 1) _ := h
| (n + 1) (m + 1) _ := le_refl _

lemma Union_bi_seq {α : Type} (A B : set α) (ha : A ≤ B) :
  Union (bi_seq A B) = B :=
begin
  apply le_antisymm,
  { sorry },
  { sorry }
end

lemma monotone_of_continuous {α : Type} (f : set α → set α)
    (hf : continuous f) :
  monotone f :=
sorry

/-! 3.2. Provide the following proof, using a similar case
distinction as for `monotone_bi_seq` above. -/

lemma monotone_iterate {α : Type} (f : set α → set α) (hf : monotone f) :
  monotone (λi, (f ^^ i) ∅) :=
sorry

/-! 3.3. Prove the main theorem. A proof sketch is given below.

We break the proof into two proofs of inclusion.

Case 1. `lfp f ≤ Union (λi, (f ^^ i) ∅)`: The key is to use the lemma `lfp_le`
together with continuity of `f`.

Case 2. `Union (λi, (f ^^ i) ∅) ≤ lfp f`: The lemma `Union_le` gives us a
natural number `i`, on which you can perform induction. We also need the lemma
`lfp_eq` to unfold one iteration of `lfp f`. -/

lemma lfp_Kleene {α : Type} (f : set α → set α) (hf : continuous f) :
  lfp f = Union (λi, (f ^^ i) ∅) :=
sorry

/- ## Question 4 (optional): A Typed, Functional Language

Up to this point, we've considered imperative languages without explicit type
systems. In this problem, we'll look at a simple example of a strongly typed
functional language and the strong guarantees we can make about its correctness.

When specifying a typed language, we are concerned with two core elements: its
*statics* and its *dynamics*. (This terminology is due to Robert Harper.) The
statics of a language are the specification of the language components that are
processed "at compile-time," prior to the execution of code. In particular, this
includes the assignment of types to terms. The dynamics of a language specify
how the language behaves at runtime; in the case of our functional language,
this will comprise a small-step operational semantics. Crucially, the statics
and dynamics must *cohere* -- be "compatible" in an appropriate sense -- to
ensure that our language is *type-safe*. (For instance, our language shouldn't
allow us to write an expression of type `τ` only for it to evaluate to an
expression of type `τ'`.) We will see two key properties for ensuring coherence:
*progress* and *preservation*.

Below, we define the abstract syntax of a simple language of *b*inary and
*n*umerical *exp*ressions (`bnexp`). It consists of two boolean constructors
(`true` and `false`), two natural-number constructors (`zero` and `succ`), two
function values (`isZero` and `double`, which behave as their names suggest),
and function application (`app`).

Some possible expressions in our language, rendered in our Lean representation,
are:
- `true` (a boolean value)
- `isZero` (a function value)
- `app double zero` (applying the function `double` to the value `zero`; in a
  standard concrete syntax, this would usually look like `double zero`)
- `app isZero (app succ zero)` (applying the function `isZero` to the result of
  applying `succ` to `zero`; this would usually be written `isZero (succ zero)`
  in standard functional syntax) -/

inductive bnexp
| true : bnexp
| false : bnexp
| zero : bnexp
| succ : bnexp
| isZero : bnexp
| double : bnexp
| app : bnexp → bnexp → bnexp

/-! We will first consider our language's statics: that is, how do we assign
types to (valid) terms in our language?

To start, we need to define the types we're working with. We define below
the types in our language's type system, of which there are three: a type of
`number`s, a type of `boolean`s, and the type `arrow τ₁ τ₂` (for any types `τ₁`
and `τ₂`) representing functions from `τ₁` to `τ₂` (akin to the Lean type
`τ₁ → τ₂`). Notice that our types are represented by an inductive (Lean) type,
just like our syntax. -/

inductive bntp
| number : bntp
| boolean : bntp
| arrow : bntp → bntp → bntp

namespace bnexp

open bntp

/-! Now that we've defined our types, we need to assign them to terms. That is,
we must define our language's statics by defining the *typing judgment* for our
language, represented by the `has_type` predicate. The constructors of
`has_type` are known as *rules* and specify different ways to assign types to
terms. (Recall that we saw some typing rules for Lean, like `Cst` and `App`,
back in Chapter 1!) Any expression assigned a type by these rules is considered
*well-typed*; we call *ill-typed* any expression `e` for which there exists no
type `τ` such that `has_type e τ` holds.

5.1. Complete the definition of `has_type` by filling in the `sorry`s below.

Note: The rest of this problem depends on the correctness of your answer.
Because of this, we provide the correct solution as a comment below. We
nevertheless encourage you to try this problem on your own before checking your
work! -/

inductive has_type : bnexp → bntp → Prop
| true : has_type true boolean
| false : has_type false sorry
| zero : has_type zero sorry
| succ : has_type succ (arrow number number)
| isZero : has_type isZero sorry
| double : has_type double sorry
| app {f x τ'} (τ) :
  has_type f (arrow τ τ') → has_type x sorry → has_type (app f x) sorry


-- Solution to 4.1:
--------------------------------------------------------------------------------
-- inductive has_type : bnexp → bntp → Prop
-- | true : has_type true boolean
-- | false : has_type false boolean
-- | zero : has_type zero number
-- | succ : has_type succ (arrow number number)
-- | isZero : has_type isZero (arrow number boolean)
-- | double : has_type double (arrow number number)
-- | app {f x τ'} (τ) :
--   has_type f (arrow τ τ') → has_type x τ → has_type (app f x) τ'
--------------------------------------------------------------------------------


-- We define notational shorthand for typing judgments: we can write `e :: τ`
-- instead of `has_type e τ`
local notation (name := bnexp_has_tp) e ` :: ` τ := has_type e τ


/-! Now that we have defined how to assign types to terms, we can identify the
types of various expressions in our language.

5.2. Provide a **forward proof** (either structured or a proof term) of the fact
that the expression `isZero (succ zero)`, as represented in our `bnexp` type,
has type `boolean`. -/

lemma type_isZero_succ_zero : app isZero (app succ zero) :: boolean :=
sorry


/-! 4.3. Prove that, given any expression `e` of type `number`, the expression
`succ (succ (double e))` has type `number`. (Feel free to use tactic mode in
this and subsequent parts.) -/

lemma type_succ_succ_double :
  ∀ (e : bnexp), e :: number → app succ (app succ (app double e)) :: number :=
sorry


/-! Next, we define our language's dynamics -- that is, how we evalute it.
Because we are defining a functional language, our small-step semantics
specifies transitions between *expressions*, not states. As an example, consider
the following example in a simple lambda calculus-like language:

  (λ x f, f x) 0 (λ y, y)
  ⇒ (λ f, f 0) (λ y, y)
  ⇒ (λ y, y) 0
  ⇒ 0

The `⇒` predicate simply indicates what reduction step to take next in order to
evaluate a given expression. The same will apply to our language of `bnexp`s.

5.4. Complete the definition of `step`, the small-step semantics for our
language of `bnexp`s, below.

Note: as with `has_type`, the rest of this question will depend on the
correctness of `step`. Therefore, we once again provide a reference solution
below. Make sure to check your work before proceeding!

Hint: for the last case, you may need to step to another expression involving
`double` -- just make sure that your recursion will terminate! -/

inductive step : bnexp → bnexp → Prop
| app_arg {f e e'} :
  step e e' → step (app f e) (app f e')
| app_isZero_zero :
  step (app isZero zero) sorry
| app_isZero_succ {e} :
  step (app isZero (app succ e)) sorry
| app_double_zero :
  step (app double zero) sorry
| app_double_succ {e} :
  step (app double (app succ e)) sorry


-- Solution to 4.4:
--------------------------------------------------------------------------------
-- inductive step : bnexp → bnexp → Prop
-- | app_arg {f e e'} :
--   step e e' → step (app f e) (app f e')
-- | app_isZero_zero :
--   step (app isZero zero) true
-- | app_isZero_succ {e} :
--   step (app isZero (app succ e)) false
-- | app_double_zero :
--   step (app double zero) zero
-- | app_double_succ {e} :
--   step (app double (app succ e)) (app succ (app succ (app double e)))
--------------------------------------------------------------------------------


-- We define our usual notation for the small-step semantics: we write `e ⇒ e'`
-- for `step e e'`.
local notation (name := bnexp_step) e ` ⇒ ` e' := step e e'


/-! Now that we have defined a statics and dynamics for our language, we must
ensure that they are mutually coherent. This is done by showing two key
properties that guarantee our language's *type safety*: progress and
preservation.

Intuitvely, progress guarantees that no well-typed expression gets "stuck"
during evaluation. More explicitly, every well-typed expression is either a
fully-evaluated value (like `3` or `true` or `[]` in Lean) or can take some step
according to our semantics. This connects our type system and our semantics in
the sense that it guarantees that, in our semantics, we've "accounted for" every
well-typed expression.

Preservation, on the other hand, says that a term preserves its original type
throughout evaluation. More formally, if an expression `e` has type `τ`, and `e`
steps to `e'`, then `e'` must also have type `τ`. (For instance, in Lean, if we
write an expression of type `ℕ`, we don't want it to evaluate to a `string`!)

Together, these properties ensure that every well-typed term can be evaluated in
a well-typed manner. (There are, of course, further properties of the `bnexp`
language we could prove, such as *termination*: the property that every
expression will eventually evaluate to a value. Feel free to think about and
even try to prove some of these other properties if you're so inclined!)

We now prove the type safety of our `bnexp` language.

5.5. Prove that preservation holds for the `bnexp` language.

Hint 1: We recommend proceeding by rule induction on the step judgment.

Hint 2: You will probably find `type_succ_succ_double` useful at some point. -/

theorem preservation {e e' : bnexp} {τ : bntp} :
  e :: τ → e ⇒ e' → e' :: τ :=
sorry


/-! **Warning**: This final problem is especially challenging and involves a
very lengthy proof! We recommend trying a few cases to get a feel for how proofs
of progress operate, but especially as this is an optional problem, please don't
sink too much time into it if you're stuck.

Lastly, we prove progress. In order to do so, we need to define what a
"fully-evaluated expression" is in our language. For this purpose, we define a
predicate that specifies *values* in the `bnexp` language. Values are
expressions that are maximally reduced; they are the "final answers" we obtain
from our computations. (In Lean, for instance, `4`, `[]`, and `(λ x, x)` are all
values.) This definition enables us to state our progress theorem.

We also supply a helper lemma, `no_hofs`, which will be of use in eliminating an
impossible case in your progress proof.

5.6. Prove that progress holds for the `bnexp` language. -/

inductive value : bnexp → Prop
| true       : value true
| false      : value false
| zero       : value zero
| succ       : value succ
| succ_n {n} : value n → value (app succ n)
| isZero     : value isZero
| double     : value double

lemma no_hofs {τ τ' τ'' : bntp} :
  ¬ ∃ e, e :: bntp.arrow τ (bntp.arrow τ' τ'') :=
begin
  intros hneg,
  cases' hneg,
  induction' h,
  assumption
end

theorem progress {e τ} : e :: τ → value e ∨ ∃ e', e ⇒ e' :=
sorry

end bnexp

end LoVe
