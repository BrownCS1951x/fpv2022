import ..lovelib

namespace LoVe
/- ## Fixpoints

A __fixpoint__ (or fixed point) of `f` is a solution for `X` in the equation

    `X = f X`

In general, fixpoints may not exist at all (e.g., `f := nat.succ`), or there may
be several fixpoints (e.g., `f := id`). But under some conditions on `f`, a
unique __least fixpoint__ and a unique __greatest fixpoint__ are guaranteed to
exist.

Consider this __fixpoint equation__:

    `X = (λ(p : ℕ → Prop) (n : ℕ), n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ p m) X`
      `= (λn : ℕ, n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ X m)`

where `X : ℕ → Prop` and
`f := (λ(p : ℕ → Prop) (n : ℕ), n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ p m)`.

The above example admits only one fixpoint. The fixpoint equation uniquely
specifies `X` as the set of even numbers.

In general, the least and greatest fixpoint may be different:

    `X = X`

Here, the least fixpoint is `(λ_, False)` and the greatest fixpoint is
`(λ_, True)`. Conventionally, `False < True`, and thus
`(λ_, False) < (λ_, True)`. Similarly, `∅ < @set.univ α` (assuming `α` is
inhabited).

For the semantics of programming languages:

* `X` will have type `set (state × state)` (which is isomorphic to
  `state → state → Prop`), representing relations between states;

* `f` will correspond to either taking one extra iteration of the loop (if the
  condition `b` is true) or the identity (if `b` is false).

Kleene's fixpoint theorem:

    `f^0(∅) ∪ f^1(∅) ∪ f^2(∅) ∪ ⋯ = lfp f`

The least fixpoint corresponds to finite executions of a program, which is all
we care about.

**Key observation**:

    Inductive predicates correspond to least fixpoints, but they are built into
    Lean's logic (the calculus of inductive constructions).


## Monotone Functions

Let `α` and `β` be types with partial order `≤`. A function `f : α → β` is
__monotone__ if

    `a₁ ≤ a₂ → f a₁ ≤ f a₂`   for all `a₁`, `a₂`

Many operations on sets (e.g., `∪`), relations (e.g., `◯`), and functions
(e.g., `λx, x`, `λ_, k`, `∘`) are monotone or preserve monotonicity.

All monotone functions `f : set α → set α` admit least and greatest fixpoints.

**Example of a nonmonotone function**:

    `f A = (if A = ∅ then set.univ else ∅)`

Assuming `α` is inhabited, we have `∅ ⊆ set.univ`, but
`f ∅ = set.univ ⊈ ∅ = f set.univ`. -/

def monotone {α β : Type} [partial_order α] [partial_order β]
  (f : α → β) : Prop :=
∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

lemma monotone_id {α : Type} [partial_order α] :
  monotone (λa : α, a) :=
begin
  intros a₁ a₂ ha,
  exact ha
end

lemma monotone_const {α β : Type} [partial_order α]
    [partial_order β] (b : β) :
  monotone (λ_ : α, b) :=
begin
  intros a₁ a₂ ha,
  exact le_refl b
end

lemma monotone_union {α β : Type} [partial_order α]
    (f g : α → set β) (hf : monotone f) (hg : monotone g) :
  monotone (λa, f a ∪ g a) :=
begin
  intros a₁ a₂ ha b hb,
  cases' hb,
  { exact or.intro_left _ (hf a₁ a₂ ha h) },
  { exact or.intro_right _ (hg a₁ a₂ ha h) }
end

/-! We will prove the following two lemmas in the exercise. -/

namespace sorry_lemmas

lemma monotone_comp {α β : Type} [partial_order α]
    (f g : α → set (β × β)) (hf : monotone f)
    (hg : monotone g) :
  monotone (λa, f a ◯ g a) :=
sorry

lemma monotone_restrict {α β : Type} [partial_order α]
    (f : α → set (β × β)) (p : β → Prop) (hf : monotone f) :
  monotone (λa, f a ⇃ p) :=
sorry

end sorry_lemmas


/-! ## Complete Lattices

To define the least fixpoint on sets, we need `⊆` and `⋂`. Complete lattices
capture this concept abstractly. A __complete lattice__ is an ordered type `α`
for which each set of type `set α` has an infimum.

More precisely, A complete lattice consists of

* a partial order `≤ : α → α → Prop` (i.e., a reflexive, transitive, and
  antisymmetric binary predicate);

* an operator `Inf : set α → α`, called __infimum__.

Moreover, `Inf A` must satisfy these two properties:

* `Inf A` is a lower bound of `A`: `Inf A ≤ b` for all `b ∈ A`;

* `Inf A` is a greatest lower bound: `b ≤ Inf A` for all `b` such that
  `∀a, a ∈ A → b ≤ a`.

**Warning:** `Inf A` is not necessarily an element of `A`.

Examples:

* `set α` is an instance w.r.t. `⊆` and `⋂` for all `α`;
* `Prop` is an instance w.r.t. `→` and `∀` (`Inf A := ∀a ∈ A, a`);
* `enat := ℕ ∪ {∞}`;
* `ereal := ℝ ∪ {- ∞, ∞}`;
* `β → α` if `α` is a complete lattice;
* `α × β` if `α`, `β` are complete lattices.

Finite example (with apologies for the ASCII art):

                Z            Inf {}           = ?
              /   \          Inf {Z}          = ?
             A     B         Inf {A, B}       = ?
              \   /          Inf {Z, A}       = ?
                Y            Inf {Z, A, B, Y} = ?

Nonexamples:

* `ℕ`, `ℤ`, `ℚ`, `ℝ`: no infimum for `∅`, `Inf ℕ`, etc.
* `erat := ℚ ∪ {- ∞, ∞}`: `Inf {q | 2 < q * q} = sqrt 2` is not in `erat`. -/

@[class] structure complete_lattice (α : Type)
  extends partial_order α : Type :=
(Inf    : set α → α)
(Inf_le : ∀A b, b ∈ A → Inf A ≤ b)
(le_Inf : ∀A b, (∀a, a ∈ A → b ≤ a) → b ≤ Inf A)

/-! For sets: -/

@[instance] def set.complete_lattice {α : Type} :
  complete_lattice (set α) :=
{ le          := (⊆),
  le_refl     := by tautology,
  le_trans    := by tautology,
  le_antisymm :=
    begin
      intros A B hAB hBA,
      apply set.ext,
      tautology
    end,
  Inf         := λX, {a | ∀A, A ∈ X → a ∈ A},
  Inf_le      := by tautology,
  le_Inf      := by tautology }


/-! ## Least Fixpoint -/

def lfp {α : Type} [complete_lattice α] (f : α → α) : α :=
complete_lattice.Inf ({a | f a ≤ a})

lemma lfp_le {α : Type} [complete_lattice α] (f : α → α)
    (a : α) (h : f a ≤ a) :
  lfp f ≤ a :=
complete_lattice.Inf_le _ _ h

lemma le_lfp {α : Type} [complete_lattice α] (f : α → α)
    (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
  a ≤ lfp f :=
complete_lattice.le_Inf _ _ h

/-! **Knaster-Tarski theorem:** For any monotone function `f`:

* `lfp f` is a fixpoint: `lfp f = f (lfp f)` (lemma `lfp_eq`);
* `lfp f` is smaller than any other fixpoint: `X = f X → lfp f ≤ X`. -/

lemma lfp_eq {α : Type} [complete_lattice α] (f : α → α)
    (hf : monotone f) :
  lfp f = f (lfp f) :=
begin
  have h : f (lfp f) ≤ lfp f :=
    begin
      apply le_lfp,
      intros a' ha',
      apply @le_trans _ _ _ (f a'),
      { apply hf,
        apply lfp_le,
        assumption },
      { assumption }
    end,
  apply le_antisymm,
  { apply lfp_le,
    apply hf,
    assumption },
  { assumption }
end
end LoVe
