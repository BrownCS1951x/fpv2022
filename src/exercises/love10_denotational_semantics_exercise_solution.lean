import ..lectures.love10_denotational_semantics_demo


/-! # LoVe Exercise 10: Denotational Semantics -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/-! ## Question 1: Monotonicity

1.1. Prove the following lemma from the lecture. -/

lemma monotone_comp {α β : Type} [partial_order α] (f g : α → set (β × β))
    (hf : monotone f) (hg : monotone g) :
  monotone (λa, f a ◯ g a) :=
begin
  intros a₁ a₂ ha b hb,
  cases' hb with m hm,
  cases' hm,
  apply exists.intro m,
  apply and.intro,
  { exact hf _ _ ha left },
  { exact hg _ _ ha right }
end

/-! 1.2. Prove its cousin. -/

lemma monotone_restrict {α β : Type} [partial_order α] (f : α → set (β × β))
    (p : β → Prop) (hf : monotone f) :
  monotone (λa, f a ⇃ p) :=
begin
  intros a₁ a₂ ha b hb,
  cases' hb,
  apply and.intro,
  { apply hf _ _ ha,
    exact left },
  { exact right }
end


/-! ## Question 2: Regular Expressions

__Regular expressions__, or __regexes__, are a highly popular tool for software
development, to analyze textual inputs. Regexes are generated by the following
grammar:

    R ::= ∅
        | ε
        | a
        | R ⬝ R
        | R + R
        | R*

Informally, the semantics of regular expressions is as follows:

* `∅` accepts nothing;
* `ε` accepts the empty string;
* `a` accepts the atom `a`;
* `R ⬝ R` accepts the concatenation of two regexes;
* `R + R` accepts either of two regexes;
* `R*` accepts arbitrary many repetitions of a regex.

Notice the rough correspondence with a WHILE language:

    `∅` ~ diverging statement (e.g., `while true do skip`)
    `ε` ~ `skip`
    `a` ~ `:=`
    `⬝` ~ `;`
    `+` ~ `if then else`
    `*` ~ `while` loop -/

inductive regex (α : Type) : Type
| nothing : regex
| empty   : regex
| atom    : α → regex
| concat  : regex → regex → regex
| alt     : regex → regex → regex
| star    : regex → regex

/-! In this exercise, we explore an alternative semantics of regular
expressions. Namely, we can imagine that the atoms represent binary relations,
instead of letters or symbols. Concatenation corresponds to composition of
relations, and alternation is union. Mathematically, regexes and binary
relations are both instances of Kleene algebras.

2.1. Complete the following translation of regular expressions to relations.

Hint: Exploit the correspondence with the WHILE language. -/

def rel_of_regex {α : Type} : regex (set (α × α)) → set (α × α)
| regex.nothing        := ∅
| regex.empty          := Id
| (regex.atom s)       := s
| (regex.concat r₁ r₂) := rel_of_regex r₁ ◯ rel_of_regex r₂
| (regex.alt r₁ r₂)    := rel_of_regex r₁ ∪ rel_of_regex r₂
| (regex.star r)       := lfp (λX, (rel_of_regex r ◯ X) ∪ Id)

/-! 2.2. Prove the following recursive equation about your definition. -/

lemma rel_of_regex_star {α : Type} (r : regex (set (α × α))) :
  rel_of_regex (regex.star r) =
  rel_of_regex (regex.alt (regex.concat r (regex.star r)) regex.empty) :=
begin
  apply lfp_eq,
  apply monotone_union,
  { apply monotone_comp,
    { exact monotone_const _ },
    { exact monotone_id } },
  { exact monotone_const _ }
end

end LoVe