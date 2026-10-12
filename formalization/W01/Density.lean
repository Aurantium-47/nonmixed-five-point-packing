import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-! A local-to-global counting lemma for arbitrary subsets of the integers.
The density is the original symmetric-interval limsup. -/

open scoped BigOperators
open Filter

namespace W01

attribute [local instance] Classical.propDecidable

noncomputable def windowCount (A : Set ℤ) (x : ℤ) (n : ℕ) : ℕ := by
  classical
  exact ∑ i ∈ Finset.range n, if x + (i : ℤ) ∈ A then 1 else 0

theorem windowCount_le (A : Set ℤ) (x : ℤ) (n : ℕ) : windowCount A x n ≤ n := by
  classical
  unfold windowCount
  calc
    _ ≤ ∑ _i ∈ Finset.range n, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs <;> omega
    _ = n := by simp

theorem windowCount_add (A : Set ℤ) (x : ℤ) (m n : ℕ) :
    windowCount A x (m + n) = windowCount A x m + windowCount A (x + m) n := by
  classical
  simp only [windowCount, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.cast_add]
  congr 2
  ring

theorem windowCount_eq_interval_card (A : Set ℤ) (x : ℤ) (n : ℕ) :
    windowCount A x n = ((Finset.Ico x (x + (n : ℤ))).filter (· ∈ A)).card := by
  classical
  rw [windowCount, ← Finset.card_filter]
  apply Finset.card_bij (fun (i : ℕ) _ => x + (i : ℤ))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at *
    exact ⟨by omega, hi.2⟩
  · intro i hi j hj hij
    omega
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_Ico] at hy
    refine ⟨(y - x).toNat, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · omega
      · convert hy.2 using 1
        omega
    · omega

noncomputable def symmetricRatio (A : Set ℤ) (N : ℕ) : ℝ :=
  (windowCount A (-(N : ℤ)) (2 * N + 1) : ℝ) / (2 * (N : ℝ) + 1)

noncomputable def upperDensity (A : Set ℤ) : ℝ :=
  Filter.limsup (symmetricRatio A) Filter.atTop

theorem symmetricRatio_eq_original (A : Set ℤ) (N : ℕ) :
    symmetricRatio A N =
      ((((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (· ∈ A)).card : ℝ) /
        (2 * (N : ℝ) + 1)) := by
  classical
  rw [symmetricRatio, windowCount_eq_interval_card]
  have hinterval : Finset.Ico (-(N : ℤ)) (-(N : ℤ) + ((2 * N + 1 : ℕ) : ℤ)) =
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    ext z
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    push_cast
    omega
  rw [hinterval]

/-- Greedy concatenation, proved by strong induction on the whole interval length. -/
theorem good_blocks_bound (A : Set ℤ) (ρ : ℝ) (L : ℕ) (hρ : 0 ≤ ρ)
    (hgood : ∀ x : ℤ, ∃ l : ℕ, 0 < l ∧ l ≤ L ∧
      (windowCount A x l : ℝ) ≤ ρ * l) :
    ∀ n : ℕ, ∀ x : ℤ, (windowCount A x n : ℝ) ≤ ρ * n + L := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x
    by_cases hn : n < L
    · have hc : (windowCount A x n : ℝ) ≤ n := by exact_mod_cast windowCount_le A x n
      have hn' : (n : ℝ) ≤ L := by exact_mod_cast (Nat.le_of_lt hn)
      have hnon : 0 ≤ ρ * n := mul_nonneg hρ (Nat.cast_nonneg n)
      linarith
    · obtain ⟨l, hl, hlL, hcount⟩ := hgood x
      have hln : l ≤ n := by omega
      have hrem : n - l < n := by omega
      have hind := ih (n - l) hrem (x + l)
      have hsplit := windowCount_add A x l (n - l)
      rw [Nat.add_sub_of_le hln] at hsplit
      have hlen : ((n - l : ℕ) : ℝ) = (n : ℝ) - l := Nat.cast_sub hln
      rw [hlen] at hind
      rw [hsplit, Nat.cast_add]
      nlinarith

theorem symmetricRatio_nonneg (A : Set ℤ) (N : ℕ) : 0 ≤ symmetricRatio A N := by
  unfold symmetricRatio
  positivity

theorem symmetricRatio_le_one (A : Set ℤ) (N : ℕ) : symmetricRatio A N ≤ 1 := by
  unfold symmetricRatio
  have h := windowCount_le A (-(N : ℤ)) (2 * N + 1)
  have h' : (windowCount A (-(N : ℤ)) (2 * N + 1) : ℝ) ≤ 2 * (N : ℝ) + 1 := by
    exact_mod_cast h
  apply (div_le_one (by positivity)).2 h'

/-- No periodicity, existence of a density limit, or restriction on the set is assumed. -/
theorem upperDensity_le_of_good_blocks (A : Set ℤ) (ρ : ℝ) (L : ℕ) (hρ : 0 ≤ ρ)
    (hgood : ∀ x : ℤ, ∃ l : ℕ, 0 < l ∧ l ≤ L ∧
      (windowCount A x l : ℝ) ≤ ρ * l) : upperDensity A ≤ ρ := by
  have hbound (N : ℕ) : symmetricRatio A N ≤ ρ + (L : ℝ) / (2 * (N : ℝ) + 1) := by
    have h := good_blocks_bound A ρ L hρ hgood (2 * N + 1) (-(N : ℤ))
    push_cast at h
    unfold symmetricRatio
    apply (div_le_iff₀ (by positivity)).2
    calc
      _ ≤ ρ * (2 * (N : ℝ) + 1) + L := h
      _ = (ρ + (L : ℝ) / (2 * (N : ℝ) + 1)) * (2 * (N : ℝ) + 1) := by
        field_simp
  have hden : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hlim : Tendsto (fun N : ℕ => ρ + (L : ℝ) / (2 * (N : ℝ) + 1)) atTop (nhds ρ) := by
    simpa using (hden.const_div_atTop (L : ℝ)).const_add ρ
  unfold upperDensity
  calc
    _ ≤ limsup (fun N : ℕ => ρ + (L : ℝ) / (2 * (N : ℝ) + 1)) atTop := by
      exact limsup_le_limsup (Eventually.of_forall hbound)
        (isCoboundedUnder_le_of_le atTop (symmetricRatio_nonneg A))
        hlim.isBoundedUnder_le
    _ = ρ := hlim.limsup_eq

end W01

#print axioms W01.windowCount_eq_interval_card
#print axioms W01.symmetricRatio_eq_original
#print axioms W01.good_blocks_bound
#print axioms W01.upperDensity_le_of_good_blocks
