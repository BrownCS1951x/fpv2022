import tactic 
import analysis.special_functions.trigonometric.arctan 

.

namespace new 

-- def complex : Type := ℝ × ℝ 

structure complex : Type :=
(r : ℝ)
(im : ℝ)

structure polar : Type := 
(angle : ℝ)
(magnitude : ℝ)
-- (mag_nn : magnitude ≥ 0)

def i : complex := {r := 0, im := 1}


def add (a b : complex) : complex :=
{ r := a.r + b.r, 
  im := a.im + b.im }

-- (a + b*i) * (c + d*i) 
-- real part: ac - bd

def mul (a b : complex) : complex := 
{ r := a.r * b.r - a.im * b.im, 
  im := a.r * b.im + a.im * b.r }

def neg (a : complex) : complex :=
{ r := -a.r, im := -a.im }


-- more fields to fill in here
instance : comm_ring complex :=
{ add := add,
  neg := neg,
  mul := mul,
  add_assoc := begin 
    intros a b c,
    simp [add],
    apply and.intro;
    ring
  end,
  zero := {r := 0, im := 0},
  zero_add := begin intro a, simp [add], cases a, refl end   }

example (a b c : complex) : a*b + c = c + b*a - a + a :=
by ring

lemma mul_def (a b : complex) : a * b = 
  { r := a.r * b.r - a.im * b.im, 
    im := a.r * b.im + a.im * b.r } :=
rfl

noncomputable def to_polar_rep (a : complex) : polar :=
{ angle := real.arctan (a.im / a.r), 
  magnitude := real.sqrt (a.r^2 + a.im^2)  }

noncomputable def of_polar_rep (p : polar) : complex :=
{ r := p.magnitude * real.cos p.angle,
  im := p.magnitude * real.sin p.angle }

theorem to_and_from (p : polar)
  (hm : p.magnitude > 0) 
  (ha1 : -(real.pi / 2) < p.angle)
  (ha2 : p.angle < real.pi / 2)
  : 
  to_polar_rep (of_polar_rep p) = p :=
begin 
  cases p,
  simp [to_polar_rep, of_polar_rep],
  apply and.intro,
  { rw [mul_div_mul_left, ← real.tan_eq_sin_div_cos, real.arctan_tan],
    assumption,
    assumption,
    linarith },
  { suffices : (p_magnitude * real.cos p_angle) ^ 2 +
     (p_magnitude * real.sin p_angle) ^ 2 = p_magnitude^2,
     { rw [this, real.sqrt_sq], linarith },
      have : (real.sin p_angle) ^2 + (real.cos p_angle) ^ 2 = 1 := 
        real.sin_sq_add_cos_sq _,
      linear_combination p_magnitude ^ 2 * this }
end 

instance : has_coe ℝ complex :=
 { coe := λ r, {r := r, im := 0} }

@[simp] lemma im_coe (r : ℝ) : (r : complex).im = 0 :=
rfl

@[simp] lemma re_coe (r : ℝ) : (r : complex).r = r :=
rfl


theorem to_polar_real (r : ℝ) (hr : r > 0) : 
  (to_polar_rep r).angle = 0 :=
begin 
  simp only [to_polar_rep, im_coe, zero_div, real.arctan_zero],
end 

def conjugate (c : complex) : complex :=
{ r := c.r,
  im := -c.im }

def reals : set complex :=
{ c : complex | c.im = 0 }

lemma mul_conjugate_is_real (c : complex) : 
  c * conjugate c ∈ reals :=
begin 
  simp [reals, conjugate, mul_def],
  ring,
end

noncomputable def magnitude (c : complex) : ℝ :=
real.sqrt ((c * conjugate c).r)


variables s t : set complex 
variable c : complex

#check c ∈ s
#check s c

#check s ∩ t
-- λ x, s x ∧ t x

#check set.mem_inter

#check s ∪ t 
-- λ x, s x ∨ t x

end new 