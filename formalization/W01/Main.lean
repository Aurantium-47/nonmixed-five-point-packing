import W01.Upper
import W01.LowerCount
import W01.Zero

namespace W01

/-- Supremum of the original symmetric upper densities of packing centers. -/
noncomputable def packingDensity (a b : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ A : Set ℤ, IsPacking a b A ∧ upperDensity A = d}

theorem exists_optimal_packing (a b : ℕ) (q r : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hdiv : (a:ℤ)-b = 5*q+r) (hr0 : 0 ≤ r) (hr5 : r < 5) :
    ∃ A : Set ℤ, IsPacking a b A ∧ upperDensity A = targetDensity a b q r := by
  by_cases hzero : r = 0
  · refine ⟨zeroCenters, zeroCenters_packing_nat a b q ha hb hcop (by omega), ?_⟩
    simpa [targetDensity, hzero] using zeroCenters_density
  by_cases hsmall : r=1 ∨ r=2
  · refine ⟨lowerCenters a b q, lowerCenters_packing_nat a b q r ha hb hcop hdiv hsmall, ?_⟩
    have hd := lower_upperDensity (a:ℤ) b q r (by omega) (by omega) hcop.isCoprime hdiv hsmall
    simpa [targetDensity, hzero, hsmall, smallRho] using hd
  · have hlarge : r=3 ∨ r=4 := by omega
    refine ⟨lowerCenters b a (-q-1),
      lowerCenters_swapped_packing (a:ℤ) b q r (by omega) (by omega) hcop.isCoprime hdiv hlarge, ?_⟩
    have hd := lower_swapped_upperDensity (a:ℤ) b q r (by omega) (by omega)
      hcop.isCoprime hdiv hlarge
    simpa [targetDensity, hzero, hsmall, largeRho] using hd

/-- Exact three-branch formula, with arbitrary nonperiodic center sets in the supremum. -/
theorem packingDensity_formula (a b : ℕ) (q r : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hdiv : (a:ℤ)-b = 5*q+r) (hr0 : 0 ≤ r) (hr5 : r < 5) :
    packingDensity a b = targetDensity a b q r := by
  obtain ⟨A, hA, hd⟩ := exists_optimal_packing a b q r ha hb hcop hdiv hr0 hr5
  have hbounded : BddAbove {d : ℝ | ∃ B : Set ℤ, IsPacking a b B ∧ upperDensity B = d} := by
    refine ⟨targetDensity a b q r, ?_⟩
    rintro d ⟨B, hB, rfl⟩
    exact packing_upper_bound B a b q r ha hb hB hdiv hr0 hr5
  apply le_antisymm
  · apply csSup_le
    · exact ⟨targetDensity a b q r, A, hA, hd⟩
    · rintro d ⟨B, hB, rfl⟩
      exact packing_upper_bound B a b q r ha hb hB hdiv hr0 hr5
  · exact le_csSup hbounded ⟨A, hA, hd⟩

/-- The quotient and remainder are computed by integer Euclidean division, including negative q. -/
theorem packingDensity_formula_euclidean (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) :
    packingDensity a b = targetDensity a b (((a:ℤ)-b)/5) (((a:ℤ)-b)%5) := by
  apply packingDensity_formula a b _ _ ha hb hcop <;> omega

end W01

#check W01.packingDensity_formula
#check W01.packingDensity_formula_euclidean
#print axioms W01.packing_upper_bound
#print axioms W01.exists_optimal_packing
#print axioms W01.packingDensity_formula
#print axioms W01.packingDensity_formula_euclidean
