import W01.Basic
import W01.PeriodicDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Group.Int.Units

/-! The period-five construction for the zero remainder branch. -/

namespace W01

attribute [local instance] Classical.propDecidable

def zeroCenters : Set ℤ := {x | (5 : ℤ) ∣ x}

theorem zero_common_residue_nonzero (a b q : ℤ)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q) : b % 5 ≠ 0 := by
  intro hb
  have hbdiv : (5 : ℤ) ∣ b := Int.dvd_iff_emod_eq_zero.mpr hb
  have hadiv : (5 : ℤ) ∣ a := by
    rw [Int.dvd_iff_emod_eq_zero]
    omega
  have hunit : IsUnit (5 : ℤ) := hcop.isUnit_of_dvd' hadiv hbdiv
  norm_num [Int.isUnit_iff] at hunit

theorem zeroCenters_avoids (a b q : ℤ)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q) :
    Avoids a b zeroCenters := by
  have hb := zero_common_residue_nonzero a b q hcop hdiv
  have hbrem : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
  intro x hx y hy hxy hd
  change (5 : ℤ) ∣ x at hx
  change (5 : ℤ) ∣ y at hy
  have hdiff : (5 : ℤ) ∣ y-x := dvd_sub hy hx
  rw [Int.dvd_iff_emod_eq_zero] at hdiff
  rw [mem_forbidden_iff] at hd
  rcases hbrem with hbrem | hbrem | hbrem | hbrem <;>
    rcases hd with hd | hd | hd | hd | hd | hd | hd | hd <;> omega

theorem zeroCenters_packing (a b q : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q) :
    IsPacking a b zeroCenters :=
  (packing_iff_avoids a b ha hb zeroCenters).mpr (zeroCenters_avoids a b q hcop hdiv)

theorem zeroCenters_packing_nat (a b : ℕ) (q : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hdiv : (a : ℤ)-b = 5*q) : IsPacking (a : ℤ) b zeroCenters :=
  zeroCenters_packing (a : ℤ) b q (by omega) (by omega) hcop.isCoprime hdiv

theorem zeroCenters_windowCount (x : ℤ) : windowCount zeroCenters x 5 = 1 := by
  have hx : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
  have h₀ : (5 : ℤ) ∣ x ↔ x % 5 = 0 := Int.dvd_iff_emod_eq_zero
  have h₁ : (5 : ℤ) ∣ x+1 ↔ x % 5 = 4 := by rw [Int.dvd_iff_emod_eq_zero]; omega
  have h₂ : (5 : ℤ) ∣ x+2 ↔ x % 5 = 3 := by rw [Int.dvd_iff_emod_eq_zero]; omega
  have h₃ : (5 : ℤ) ∣ x+3 ↔ x % 5 = 2 := by rw [Int.dvd_iff_emod_eq_zero]; omega
  have h₄ : (5 : ℤ) ∣ x+4 ↔ x % 5 = 1 := by rw [Int.dvd_iff_emod_eq_zero]; omega
  simp only [windowCount, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, zeroCenters, Set.mem_setOf_eq, add_zero, zero_add, h₀, h₁, h₂, h₃, h₄]
  rcases hx with hx | hx | hx | hx | hx <;> simp only [hx] <;> norm_num

theorem zeroCenters_density : upperDensity zeroCenters = (1 : ℝ)/5 := by
  simpa using upperDensity_eq_of_constant_blocks zeroCenters 5 1 (by decide) zeroCenters_windowCount

end W01

#print axioms W01.zeroCenters_packing_nat
#print axioms W01.zeroCenters_windowCount
#print axioms W01.zeroCenters_density
