import ..lectures.love02_backward_proofs_demo


/-! # LoVe Exercise 2: Backward Proofs -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

namespace backward_proofs


/-! ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma I (a : Prop) :
  a → a :=
begin
  intro ha,
  exact ha
end

lemma K (a b : Prop) :
  a → b → b :=
begin
  intros ha hb,
  exact hb
end

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
begin
  intros hg hb ha,
  apply hg,
  exact ha,
  exact hb
end

lemma proj_1st (a : Prop) :
  a → a → a :=
begin
  intros ha ha',
  exact ha
end

/-! Please give a different answer than for `proj_1st`: -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
begin
  intros ha ha',
  exact ha'
end

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
begin
  intros hg ha hf hb,
  apply hg,
  exact ha,
  exact hb
end

/-! 1.2. Prove the contraposition rule using basic tactics. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
begin
  intros hab hnb ha,
  apply hnb,
  apply hab,
  apply ha
end

/-! 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap₂` in the lecture, might be
necessary. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
begin
  apply iff.intro,
  { intro h,
    apply and.intro,
    { intro x,
      apply and.elim_left,
      apply h },
    { intro x,
      apply and.elim_right,
      apply h } },
  { intros h x,
    apply and.intro,
    { apply and.elim_left h },
    { apply and.elim_right h } }
end

end backward_proofs

namespace existentials

/-! ## Question 2: Existentials

In this section, you'll practice using `exists.intro` and `exists.elim`.
-/

#check @exists.intro
#check @exists.elim

/-! 2.1. Prove that we can "flip" the existential and universal quantifiers.
(Note that this only works in one direction!)
-/

lemma website_icon {α β : Sort _} {p : α → β → Prop} :
  (∃ a, ∀ b, p a b) → (∀ b, ∃ a, p a b) :=
begin
  intros h b,
  apply exists.elim h,
  intros w hw,
  apply exists.intro w,
  apply hw,
end

/-! 2.2 Prove, using the definition of `isEven` below, that adding two to an
even number gives another even number.
-/

-- Here is a definition and helper lemma for exercise 2.2
def isEven (n : ℕ) := ∃ k, n = 2 * k
lemma add_two_eq (m n : ℕ) : m = n → m + 2 = n + 2 :=
congr_arg (λ x, x + 2)

-- You may also find the following lemmas helpful:
#check mul_add
#check mul_one

lemma even_add_two : ∀ n : ℕ, isEven n → isEven (n + 2) :=
begin
  intros n hn,
  apply exists.elim hn,
  intros w hw,
  apply exists.intro (w + 1),
  rw [mul_add, mul_one],
  apply add_two_eq,
  apply hw,
end

/- 2.3. Prove that two consecutive natural numbers cannot be even.

Hints:
* You can use `and.elim` to extract the two sides of a conjunction.
* `eq.symm` reverses the sides of an equality.
* If you have a hypothesis `h : a = b` and want to replace `b` with `a` in your
  goal (instead of `a` with `b`), use `rw ←h` (note the `←`).
-/
axiom no_odd_doubles : ∀ (n : ℕ), ¬ ∃ (m : ℕ), 2 * n = m + 1

lemma t (n : ℕ) : ¬(isEven n ∧ isEven (n + 1)) :=
begin
  intros hneg,
  apply and.elim hneg,
  intros hright hleft,
  apply exists.elim hright,
  intros w hw,
  apply exists.elim hleft,
  intros v hv,
  apply no_odd_doubles v,
  apply exists.intro (2*w),
  rw ←hw,
  apply eq.symm,
  apply hv,
end

end existentials

namespace backward_proofs

/-! ## Question 3: Natural Numbers

3.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

lemma mul_zero (n : ℕ) :
  mul 0 n = 0 :=
begin
  induction' n,
  { refl },
  { simp [add, mul, ih] }
end

lemma mul_succ (m n : ℕ) :
  mul (nat.succ m) n = add (mul m n) n :=
begin
  induction' n,
  { refl },
  { simp [add, add_succ, add_assoc, mul, ih] }
end

/-! 3.2. Prove commutativity and associativity of multiplication using the
`induction'` tactic. Choose the induction variable carefully. -/

lemma mul_comm (m n : ℕ) :
  mul m n = mul n m :=
begin
  induction' m,
  { simp [mul, mul_zero] },
  { simp [mul, mul_succ, ih],
    cc }
end

lemma mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
begin
  induction' n,
  { refl },
  { simp [mul, mul_add, ih] }
end

/-! 3.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

lemma add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
begin
  rw mul_comm _ n,
  rw mul_add
end


/-! ## Question 4 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def excluded_middle : Prop :=
∀a : Prop, a ∨ ¬ a

def peirce : Prop :=
∀a b : Prop, ((a → b) → a) → a

def double_negation : Prop :=
∀a : Prop, (¬¬ a) → a

/-! For the proofs below, please avoid using lemmas from Lean's `classical`
namespace, as this would defeat the purpose of the exercise.

4.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `or.elim` and `false.elim`. You can use
`rw excluded_middle` to unfold the definition of `excluded_middle`,
and similarly for `peirce`. -/

lemma peirce_of_em :
  excluded_middle → peirce :=
begin
  rw excluded_middle,
  rw peirce,
  intro hem,
  intros a b haba,
  apply or.elim (hem a),
  { intro,
    assumption },
  { intro hna,
    apply haba,
    intro ha,
    apply false.elim,
    apply hna,
    assumption }
end

/-! 4.2 (**optional**). Prove the following implication using tactics. -/

lemma dn_of_peirce :
  peirce → double_negation :=
begin
  rw peirce,
  rw double_negation,
  intros hpeirce a hnna,
  apply hpeirce a false,
  intro hna,
  apply false.elim,
  apply hnna,
  exact hna
end

/-! We leave the remaining implication for the homework: -/

namespace sorry_lemmas

lemma em_of_dn :
  double_negation → excluded_middle :=
sorry

end sorry_lemmas

end backward_proofs

end LoVe
