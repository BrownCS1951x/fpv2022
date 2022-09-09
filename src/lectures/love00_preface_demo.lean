
import data.nat.prime
import tactic.linarith

set_option pp.generalized_field_notation false

/-! # LoVe Preface

## Proof Assistants

Proof assistants (also called interactive theorem provers)

* check and help develop formal proofs;
* can be used to prove big theorems, not only logic puzzles;
* can be tedious to use;
* are highly addictive (think video games).

A selection of proof assistants, classified by logical foundations:

* set theory: Isabelle/ZF, Metamath, Mizar;
* simple type theory: HOL4, HOL Light, Isabelle/HOL;
* **dependent type theory**: Agda, Coq, **Lean**, Matita, PVS.


## Success Stories

Mathematics:

* the four-color theorem (in Coq);
* the odd-order theorem (in Coq);
* the Kepler conjecture (in HOL Light and Isabelle/HOL).

Computer science:

* hardware
* operating systems
* programming language theory
* compilers
* security


## Lean

Lean is a proof assistant developed primarily by Leonardo de Moura (Microsoft
Research) since 2012.

Its mathematical library, `mathlib`, is developed by a user community.

We use community version 3.43.0. We use its basic libraries, `mathlib`, and
`LoVelib`. Lean is a research project.

Strengths:

* highly expressive logic based on a dependent type theory called the
  **calculus of inductive constructions**;
* extended with classical axioms and quotient types;
* metaprogramming framework;
* modern user interface;
* documentation;
* open source;
* wonderful user community.


## This Course

### Web Site

    https://BrownCS1951x.github.io 


### Repository (Demos, Exercises, Homework)

    https://github.com/BrownCS1951x/fpv2022

The file you are currently looking at is a demo. 
For each chapter of the Hitchhiker's Guide, there will be approximately
one demo, one exercise sheet, and one homework.

* Demos will be covered in class. These are "lecture notes."
  We'll post skeletons of the demos before class, and completed demos after class.

* Exercises are ungraded practice problems for you to use to learn.
  Sometimes we'll cover exercise problems in class. Occasionally we may run 
  class like a lab, giving you time to work on exercise problems with us around.

* Homeworks are for you to do on your own, and submit via Gradescope.


### The Hitchhiker's Guide to Logical Verification

    https://cs.brown.edu/courses/cs1951x/static_files/main.pdf

The lecture notes consist of a preface and 13 chapters. They cover the same
material as the corresponding lectures but with more details. Sometimes there
will not be enough time to cover everything in class, so reading the lecture
notes will be necessary.

Download this version, not others that you might find online!


## Our Goal

We want you to

* master fundamental theory and techniques in interactive theorem proving;
* familiarize yourselves with some application areas;
* develop some practical skills you can apply on a larger project (as a hobby,
  for an MSc or PhD, or in industry);
* feel ready to move to another proof assistant and apply what you have learned;
* understand the domain well enough to start reading scientific papers.

This course is neither a pure logical foundations course nor a Lean tutorial.
Lean is our vehicle, not an end in itself.

-/


open nat
open_locale nat

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, nat.prime p :=
begin 
  intro N, 
  let M := N! + 1,
  let q := min_fac M,

  have hq : nat.prime q := begin 
    refine min_fac_prime _,
    have hn : N! > 0 := factorial_pos N,
    linarith
  end,

  use q,

  split,

  { by_contradiction,
    have h1 : q ∣ N! + 1 := min_fac_dvd M,
    have h1' : q ≤ N := le_of_not_ge h,
    have h2 : q ∣ N! := (prime.dvd_factorial hq).mpr h1',
    have h3 : q ∣ 1 := (nat.dvd_add_right h2).mp h1,
    exact nat.prime.not_dvd_one hq h3 },

  { exact hq },
end

#print infinitude_of_primes

#eval min_fac 30
