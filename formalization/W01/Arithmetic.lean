import Mathlib.Tactic

/-! The integer obstruction and four nonzero remainder branches.
These are arithmetic lemmas; the counting and equality hypotheses must
be supplied by the combinatorial proof, not by an axiom. -/

namespace W01

theorem small_remainder_alternative
    (a b q r F₁ F₂ : ℤ)
    (hdiv : a - b = 5 * q + r) (hr : r = 1 ∨ r = 2)
    (hsum : F₁ + F₂ ≤ a + b)
    (heq : F₁ + F₂ = a + b → ∃ t : ℤ, F₁ = b + 2 * t) :
    F₁ ≤ b + 2 * q ∨ F₂ ≤ b + 3 * q := by
  by_contra h
  push_neg at h
  rcases hr with hr | hr
  · omega
  · have he : F₁ + F₂ = a + b := by omega
    obtain ⟨t, ht⟩ := heq he
    omega

theorem large_remainder_alternative
    (a b q r F₁ F₂ : ℤ)
    (hdiv : a - b = 5 * q + r) (hr : r = 3 ∨ r = 4)
    (hsum : F₁ + F₂ ≤ a + b)
    (heq : F₁ + F₂ = a + b → ∃ t : ℤ, F₁ = b + 2 * t) :
    F₁ ≤ a - 3 * (q + 1) ∨ F₂ ≤ a - 2 * (q + 1) := by
  by_contra h
  push_neg at h
  rcases hr with hr | hr
  · have he : F₁ + F₂ = a + b := by omega
    obtain ⟨t, ht⟩ := heq he
    omega
  · omega

theorem small_cross_product (a b q r : ℤ) (h : a - b = 5 * q + r) :
    (b + 2 * q) * (3 * a + 2 * b) -
      (b + 3 * q) * (2 * a + 3 * b) = b * r := by
  have ha : a = b + 5 * q + r := by omega
  rw [ha]
  ring

theorem large_cross_product (a b q r : ℤ) (h : a - b = 5 * q + r) :
    (a - 2 * (q + 1)) * (2 * a + 3 * b) -
      (a - 3 * (q + 1)) * (3 * a + 2 * b) = a * (5 - r) := by
  have ha : a = b + 5 * q + r := by omega
  rw [ha]
  ring

theorem small_numerator_positive (a b q r : ℤ)
    (ha : 0 < a) (hb : 0 < b) (h : a - b = 5 * q + r)
    (hr : r = 1 ∨ r = 2) : 0 < b + 2 * q := by
  rcases hr with hr | hr <;> omega

theorem swapped_division (a b q r : ℤ) (h : a - b = 5 * q + r) :
    b - a = 5 * (-q - 1) + (5 - r) := by omega

theorem small_local_real (a b q r F₁ F₂ : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hdiv : a - b = 5 * q + r) (hr : r = 1 ∨ r = 2)
    (hsum : F₁ + F₂ ≤ a + b)
    (heq : F₁ + F₂ = a + b → ∃ t : ℤ, F₁ = b + 2 * t) :
    (F₁ : ℝ) ≤ ((b + 2 * q : ℤ) : ℝ) / ((2 * a + 3 * b : ℤ) : ℝ) * (2 * a + 3 * b : ℤ) ∨
    (F₂ : ℝ) ≤ ((b + 2 * q : ℤ) : ℝ) / ((2 * a + 3 * b : ℤ) : ℝ) * (3 * a + 2 * b : ℤ) := by
  have hn₁ : (0 : ℝ) < ((2 * a + 3 * b : ℤ) : ℝ) := by exact_mod_cast (show 0 < 2*a+3*b by omega)
  have hc : (((b + 2*q) * (3*a+2*b) - (b+3*q) * (2*a+3*b) : ℤ) : ℝ) = ((b*r:ℤ):ℝ) :=
    congrArg (Int.cast : ℤ → ℝ) (small_cross_product a b q r hdiv)
  push_cast at hc
  have hbr : (0 : ℝ) ≤ ((b*r:ℤ):ℝ) := by
    exact_mod_cast (mul_nonneg (le_of_lt hb) (by rcases hr with h | h <;> omega : 0 ≤ r))
  push_cast at hbr
  rcases small_remainder_alternative a b q r F₁ F₂ hdiv hr hsum heq with hF | hF
  · left
    rw [div_mul_cancel₀ _ (ne_of_gt hn₁)]
    exact_mod_cast hF
  · right
    have hF' : (F₂ : ℝ) ≤ ((b + 3*q : ℤ) : ℝ) := by exact_mod_cast hF
    calc
      (F₂ : ℝ) ≤ ((b + 3*q : ℤ) : ℝ) := hF'
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hn₁).2
        push_cast
        nlinarith

theorem large_local_real (a b q r F₁ F₂ : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hdiv : a - b = 5 * q + r) (hr : r = 3 ∨ r = 4)
    (hsum : F₁ + F₂ ≤ a + b)
    (heq : F₁ + F₂ = a + b → ∃ t : ℤ, F₁ = b + 2 * t) :
    (F₁ : ℝ) ≤ ((a - 2 * (q+1) : ℤ) : ℝ) / ((3 * a + 2 * b : ℤ) : ℝ) * (2 * a + 3 * b : ℤ) ∨
    (F₂ : ℝ) ≤ ((a - 2 * (q+1) : ℤ) : ℝ) / ((3 * a + 2 * b : ℤ) : ℝ) * (3 * a + 2 * b : ℤ) := by
  have hn₂ : (0 : ℝ) < ((3 * a + 2 * b : ℤ) : ℝ) := by exact_mod_cast (show 0 < 3*a+2*b by omega)
  have hc : (((a-2*(q+1))*(2*a+3*b)-(a-3*(q+1))*(3*a+2*b):ℤ):ℝ) = ((a*(5-r):ℤ):ℝ) :=
    congrArg (Int.cast : ℤ → ℝ) (large_cross_product a b q r hdiv)
  push_cast at hc
  have har : (0 : ℝ) ≤ ((a*(5-r):ℤ):ℝ) := by
    exact_mod_cast (mul_nonneg (le_of_lt ha) (by rcases hr with h | h <;> omega : 0 ≤ 5-r))
  push_cast at har
  rcases large_remainder_alternative a b q r F₁ F₂ hdiv hr hsum heq with hF | hF
  · left
    have hF' : (F₁ : ℝ) ≤ ((a - 3*(q+1) : ℤ) : ℝ) := by exact_mod_cast hF
    calc
      (F₁ : ℝ) ≤ ((a - 3*(q+1) : ℤ) : ℝ) := hF'
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hn₂).2
        push_cast
        nlinarith
  · right
    rw [div_mul_cancel₀ _ (ne_of_gt hn₂)]
    exact_mod_cast hF

end W01

#print axioms W01.small_remainder_alternative
#print axioms W01.large_remainder_alternative
#print axioms W01.small_cross_product
#print axioms W01.large_cross_product
#print axioms W01.small_numerator_positive
#print axioms W01.swapped_division
#print axioms W01.small_local_real
#print axioms W01.large_local_real
