import W01.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith

/-! The signed integer obstruction for the periodic lower construction.
No order between a and b, or sign restriction on q, is imposed. -/

namespace W01

theorem lower_relation_trivial
    (a b q r c t i j z : ℤ)
    (ha : 0 < a) (hcop : IsCoprime a b)
    (hdiv : a - b = 5*q+r) (hr : r = 1 ∨ r = 2)
    (hcdef : c = b+2*q) (hc : 0 < c)
    (ht : |t| < c) (hi0 : 0 ≤ i) (hi2 : i ≤ 2)
    (hj0 : 0 ≤ j) (hj2 : j ≤ 2)
    (hrel : t*(a-b) = i*a+j*b+z*(2*a+3*b)) :
    t = 0 ∧ i = 0 ∧ j = 0 ∧ z = 0 := by
  have hprod : a*(t-2*z-i) = b*(t+3*z+j) := by nlinarith [hrel]
  have hdvd : a ∣ t+3*z+j := hcop.dvd_of_dvd_mul_left ⟨t-2*z-i, hprod.symm⟩
  obtain ⟨p, hap⟩ := hdvd
  have hbp : t-2*z-i = b*p := by
    apply mul_left_cancel₀ (ne_of_gt ha)
    calc
      a*(t-2*z-i) = b*(t+3*z+j) := hprod
      _ = b*(a*p) := by rw [hap]
      _ = a*(b*p) := by ring
  let u : ℤ := z-q*p
  have hrp : r*p = 5*u+i+j := by
    dsimp [u]
    calc
      r*p = (a-b)*p-5*q*p := by rw [hdiv]; ring
      _ = (a*p-b*p)-5*q*p := by ring
      _ = (t+3*z+j-(t-2*z-i))-5*q*p := by rw [← hap, ← hbp]
      _ = 5*(z-q*p)+i+j := by ring
  have htp : t = c*p+2*u+i := by
    dsimp [u]
    rw [hcdef]
    nlinarith [hbp]
  obtain ⟨htlo, hthi⟩ := abs_lt.mp ht
  rcases lt_trichotomy p 0 with hp | hp | hp
  · have hu : u ≤ -1 := by
      rcases hr with rfl | rfl <;> omega
    have hcp : c*p ≤ -c := by nlinarith
    omega
  · have hu : u = 0 := by rw [hp] at hrp; omega
    have hi : i = 0 := by rw [hp] at hrp; omega
    have hj : j = 0 := by rw [hp] at hrp; omega
    have hz : z = 0 := by dsimp [u] at hu; rw [hp] at hu; omega
    exact ⟨by rw [hp] at htp; omega, hi, hj, hz⟩
  · have hu : 0 ≤ u := by
      rcases hr with rfl | rfl <;> omega
    have hcp : c ≤ c*p := by nlinarith
    omega

/-- Centers in the source's lower-bound construction, with signed q. -/
def lowerCenters (a b q : ℤ) : Set ℤ :=
  {x | ∃ t z : ℤ, 0 ≤ t ∧ t < b+2*q ∧
    x = t*(a-b)+z*(2*a+3*b)}

theorem lowerCenters_periodic (a b q x : ℤ) :
    x+(2*a+3*b) ∈ lowerCenters a b q ↔ x ∈ lowerCenters a b q := by
  constructor
  · rintro ⟨t, z, ht0, htc, he⟩
    refine ⟨t, z-1, ht0, htc, ?_⟩
    nlinarith [he]
  · rintro ⟨t, z, ht0, htc, he⟩
    refine ⟨t, z+1, ht0, htc, ?_⟩
    nlinarith [he]

/-- Distinct allowed indices represent distinct residues modulo the period. -/
theorem lower_representation_unique
    (a b q r s t u v : ℤ)
    (ha : 0 < a) (hcop : IsCoprime a b)
    (hdiv : a-b = 5*q+r) (hr : r = 1 ∨ r = 2)
    (hc : 0 < b+2*q)
    (hs0 : 0 ≤ s) (hsc : s < b+2*q)
    (ht0 : 0 ≤ t) (htc : t < b+2*q)
    (heq : s*(a-b)+u*(2*a+3*b) = t*(a-b)+v*(2*a+3*b)) :
    s = t ∧ u = v := by
  have habs : |s-t| < b+2*q := by rw [abs_lt]; omega
  have hrel : (s-t)*(a-b) = (0:ℤ)*a+0*b+(v-u)*(2*a+3*b) := by
    nlinarith [heq]
  obtain ⟨hd, _, _, hz⟩ := lower_relation_trivial a b q r (b+2*q)
    (s-t) 0 0 (v-u) ha hcop hdiv hr rfl hc habs
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hrel
  constructor <;> omega

theorem lowerCenters_avoids
    (a b q r : ℤ)
    (ha : 0 < a) (hcop : IsCoprime a b)
    (hdiv : a-b = 5*q+r) (hr : r = 1 ∨ r = 2)
    (hc : 0 < b+2*q) : Avoids a b (lowerCenters a b q) := by
  intro x hx y hy _ hbad
  obtain ⟨s, u, hs0, hsc, hx⟩ := hx
  obtain ⟨t, v, ht0, htc, hy⟩ := hy
  obtain ⟨i, j, hi0, hi2, hj0, hj2, hij, hd⟩ :=
    (forbidden_coefficients a b (y-x)).mp hbad
  have habs : |t-s| < b+2*q := by rw [abs_lt]; omega
  have hrel : (t-s)*(a-b) = i*a+j*b+(u-v)*(2*a+3*b) := by
    nlinarith [hx, hy, hd]
  obtain ⟨_, hi, hj, _⟩ := lower_relation_trivial a b q r (b+2*q)
    (t-s) i j (u-v) ha hcop hdiv hr rfl hc habs hi0 hi2 hj0 hj2 hrel
  omega

theorem lowerCenters_packing
    (a b q r : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q+r)
    (hr : r = 1 ∨ r = 2) : IsPacking a b (lowerCenters a b q) := by
  have hc : 0 < b+2*q := by rcases hr with rfl | rfl <;> omega
  exact (packing_iff_avoids a b ha hb _).mpr
    (lowerCenters_avoids a b q r ha hcop hdiv hr hc)

theorem lowerCenters_packing_nat
    (a b : ℕ) (q r : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) (hdiv : (a : ℤ)-b = 5*q+r)
    (hr : r = 1 ∨ r = 2) :
    IsPacking (a : ℤ) b (lowerCenters (a : ℤ) b q) := by
  exact lowerCenters_packing (a : ℤ) b q r (by omega) (by omega)
    hcop.isCoprime hdiv hr

theorem lowerCenters_swapped_packing
    (a b q r : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q+r)
    (hr : r = 3 ∨ r = 4) :
    IsPacking a b (lowerCenters b a (-q-1)) := by
  have hs : b-a = 5*(-q-1)+(5-r) := by omega
  have hrs : 5-r = 1 ∨ 5-r = 2 := by omega
  have hp := lowerCenters_packing b a (-q-1) (5-r) hb ha hcop.symm hs hrs
  apply (packing_iff_avoids a b ha hb _).mpr
  exact (avoids_comm b a _).mp ((packing_iff_avoids b a hb ha _).mp hp)

end W01

#print axioms W01.lower_relation_trivial
#print axioms W01.lowerCenters_periodic
#print axioms W01.lower_representation_unique
#print axioms W01.lowerCenters_avoids
#print axioms W01.lowerCenters_packing
#print axioms W01.lowerCenters_packing_nat
#print axioms W01.lowerCenters_swapped_packing
