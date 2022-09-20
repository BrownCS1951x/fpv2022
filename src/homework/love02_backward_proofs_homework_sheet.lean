import ..exercises.love02_backward_proofs_exercise_sheet


/-! # LoVe Homework 2: Backward Proofs

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

namespace backward_proofs


/-! ## Question 1 (4 points): Connectives and Quantifiers

1.1 (3 points). Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma B (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
sorry

lemma S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
sorry

lemma more_nonsense (a b c : Prop) :
  (c → (a → b) → a) → c → b → a :=
sorry

lemma even_more_nonsense (a b c : Prop) :
  (a → a → b) → (b → c) → a → b → c :=
sorry

/-! 1.2 (1 point). Prove the following lemma using basic tactics. -/

lemma weak_peirce (a b : Prop) :
  ((((a → b) → a) → a) → b) → b :=
sorry


/-! ## Question 2 (6 points): Logical Connectives

2.1 (2 points). Prove the following properties about logical connectives using
basic tactics.

Hints:

* Keep in mind that `¬ a` is the same as `a → false`. You can start by invoking
  `rw not_def` if this helps you.

* You will need to apply the elimination rules for `∨` and `false` at some
  point. -/

lemma about_implication (a b : Prop) :
  ¬ a ∨ b → a → b :=
sorry

lemma about_negation (a b : Prop) : 
  a → ¬ (¬ a ∧ b) :=
sorry 

/-! 2.2 (2 points). Prove the missing link in our chain of classical axiom
implications.

Hints:

* You can use `rw double_negation` to unfold the definition of
  `double_negation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check excluded_middle
#check peirce
#check double_negation

lemma em_of_dn :
  double_negation → excluded_middle :=
sorry

/-! 2.3 (2 points). We have proved three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check peirce_of_em
#check dn_of_peirce
#check em_of_dn

-- enter your solution here

end backward_proofs


/-! ## Question 3 (3 points): Equality

You may hear it said that equality is the smallest *reflexive*, *symmetric*, 
*transitive* relation. The following exercise shows that in the presence of 
reflexivity, the rules for symmetry and transitivity are equivalent to a single
rule, "symmtrans". -/

axiom symmtrans {A : Type} {a b c : A} : a = b → c = b → a = c

-- You can now use `symmtrans` as a rule.

example (A : Type) (a b c : A) (h1 : a = b) (h2 : c = b) : a = c :=
begin 
  apply symmtrans,
  apply h1,
  apply h2
end 


section

variable {A : Type}
variables {a b c : A}

/-! Replace the `sorry`s below with proofs, using `symmtrans` and `rfl`, without
using `eq.symm` or `eq.trans`. -/

theorem my_symm (h : b = a) : a = b :=
sorry

theorem my_trans (h1 : a = b) (h2 : b = c) : a = c :=
sorry 

end

/-! ## Question 4 (3 points): Pythagorean Triples

Recall that a Pythagorean triple is a 'triple' of three natural numbers a, b,
and c such that a² + b² = c², i.e. integer sides of a right triangle.-/

def isPythagoreanTriple (a b c : ℕ) : Prop :=
  a^2 + b^2 = c^2

/- By assuming Fermat's Last Theorem
(https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem), we can show that if
`a`, `b`, and `c` form a Pythagorean triple, then `a`, `b`, and `c` can't all be
perfect squares. Use the definitions below to prove this. -/

axiom fermats_last_theorem (x y n : ℕ) :
  (n ≥ 3) → ¬∃ (z : ℕ), x^n + y^n = z^n

def isSquare (n : ℕ) : Prop := ∃ (u : ℕ), n = u^2

-- You may use the following lemma in your proof.
lemma square_square (a b c : ℕ) :
  (a^2)^2 + (b^2)^2 = (c^2)^2 → a^4 + b^4 = c^4 := 
by intro h; rw [←pow_mul, ←pow_mul, ←pow_mul] at h; exact h

/-! Hints:
* You can use `and.elim` to extract both terms from a conjunction.
* If you have a hypothesis `h : a = b` and want to replace `b` with `a` in your
  goal (instead of `a` with `b`), use `rw ←h` (note the `←`).
* You can use `dec_trivial` to prove that 4 ≥ 3.
-/

theorem pythagoren_triple_not_all_squares (a b c : ℕ) :
  isPythagoreanTriple a b c → ¬(isSquare a ∧ isSquare b ∧ isSquare c) :=
sorry


end LoVe
