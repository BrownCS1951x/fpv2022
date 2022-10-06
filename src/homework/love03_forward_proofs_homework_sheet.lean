import ..exercises.love02_backward_proofs_exercise_sheet


/-! # LoVe Homework 3: Forward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1 (6 points): Connectives and Quantifiers

1.1 (2 points). We have proved or stated three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. Prove the three
missing implications using structured proofs, exploiting the three theorems we
already have. -/

namespace backward_proofs

#check peirce_of_em
#check dn_of_peirce
#check sorry_lemmas.em_of_dn

lemma peirce_of_dn :
  double_negation → peirce :=
sorry

lemma em_of_peirce :
  peirce → excluded_middle :=
sorry

lemma dn_of_em :
  excluded_middle → double_negation :=
sorry

end backward_proofs

/-! 1.2 (4 points). Supply a structured proof of the commutativity of `∧` under
an `∃` quantifier, using no other lemmas than the introduction and elimination
rules for `∃`, `∧`, and `↔`. -/

lemma exists_and_commute {α : Type} (p q : α → Prop) :
  (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
sorry


/-! ## Question 2 (4 points): Logic Puzzles

Recall the following tactical proof: -/

lemma weak_peirce :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
begin
  intros a b habaab,
  apply habaab,
  intro habaa,
  apply habaa,
  intro ha,
  apply habaab,
  intro haba,
  apply ha
end

/-! 2.1 (1 point). Prove the same lemma again, this time by providing a proof
term.

Hint: There is an easy way. Anything goes! -/

lemma weak_peirce₂ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
sorry

/-! 2.2 (2 points). Prove the same lemma again, this time by providing a
structured proof, with `assume`s and `show`s. -/

lemma weak_peirce₃ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
sorry

/-! 2.3 (1 point). In a certain faraway village, there is only one barber for
the whole town. He shaves all those who do not shave themselves. Does the barber
shave himself? 

Show that this premise implies `false`.
-/
axiom not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P)


example (Q : Prop) : ¬ (Q ↔ ¬ Q) :=
not_iff_not_self Q

section
  variable Person : Type
  variable shaves : Person → Person → Prop
  variable barber : Person
  variable h : ∀ x, shaves barber x ↔ ¬ shaves x x
  include h
  -- Show the following:
  example : false :=
    sorry
end

/-! 
Optional extra challenge: we don't need `not_iff_not_self` to be an axiom. 
State it as a lemma and prove it! 
Extra extra challenge: prove it without using `classical.em` or `classical.by_contradiction`.
-/

/-! ## Question 3 (2 points): Calc Mode
Use `calc` mode to prove that the difference of squares formula holds on the
integers. (In this particular problem, working on the integers is necessary, but in
practice not much different from working on ℕ.)
You might find some or all of the following subtraction lemmas useful!
-/
#check mul_sub
#check sub_add_eq_sub_sub
#check sub_self
#check add_sub_assoc
#check mul_comm
#check add_mul

lemma difference_of_squares (a b : ℤ) :
  (a + b) * (a - b) = a * a - b * b :=
  sorry

end LoVe
