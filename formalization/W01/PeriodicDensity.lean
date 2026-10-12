import W01.Density

open scoped BigOperators
open Filter

namespace W01

attribute [local instance] Classical.propDecidable

theorem windowCount_add_compl (A : Set ℤ) (x : ℤ) (n : ℕ) :
    windowCount A x n + windowCount Aᶜ x n = n := by
  classical
  unfold windowCount
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _i ∈ Finset.range n, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : x + (i : ℤ) ∈ A <;> simp [h]
    _ = n := by simp

theorem symmetricRatio_tendsto_of_constant_blocks (A : Set ℤ) (n c : ℕ) (hn : 0 < n)
    (hc : ∀ x : ℤ, windowCount A x n = c) :
    Tendsto (symmetricRatio A) atTop (nhds ((c : ℝ) / n)) := by
  let ρ : ℝ := (c : ℝ) / n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn : c ≤ n := by simpa [hc 0] using windowCount_le A 0 n
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by
    dsimp [ρ]
    apply (div_le_one hn').2
    exact_mod_cast hcn
  have hgood (x : ℤ) : ∃ l : ℕ, 0 < l ∧ l ≤ n ∧
      (windowCount A x l : ℝ) ≤ ρ * l := by
    refine ⟨n, hn, le_rfl, ?_⟩
    rw [hc x]
    dsimp [ρ]
    rw [div_mul_cancel₀ _ (ne_of_gt hn')]
  have hgoodc (x : ℤ) : ∃ l : ℕ, 0 < l ∧ l ≤ n ∧
      (windowCount Aᶜ x l : ℝ) ≤ (1-ρ) * l := by
    refine ⟨n, hn, le_rfl, ?_⟩
    have hadd := windowCount_add_compl A x n
    rw [hc x] at hadd
    have hadd' : (c : ℝ) + windowCount Aᶜ x n = n := by exact_mod_cast hadd
    dsimp [ρ]
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hn')]
    linarith
  have hu (x : ℤ) (k : ℕ) : (windowCount A x k : ℝ) ≤ ρ*k+n :=
    good_blocks_bound A ρ n hρ hgood k x
  have hl (x : ℤ) (k : ℕ) : ρ*k-n ≤ (windowCount A x k : ℝ) := by
    have h := good_blocks_bound Aᶜ (1-ρ) n (by linarith) hgoodc k x
    have hadd : (windowCount A x k : ℝ) + windowCount Aᶜ x k = k := by
      exact_mod_cast windowCount_add_compl A x k
    nlinarith
  have hlo (N : ℕ) : ρ - (n : ℝ)/(2*(N:ℝ)+1) ≤ symmetricRatio A N := by
    have h := hl (-(N:ℤ)) (2*N+1)
    push_cast at h
    unfold symmetricRatio
    apply (le_div_iff₀ (by positivity)).2
    calc
      _ = ρ*(2*(N:ℝ)+1)-n := by field_simp
      _ ≤ _ := h
  have hup (N : ℕ) : symmetricRatio A N ≤ ρ + (n : ℝ)/(2*(N:ℝ)+1) := by
    have h := hu (-(N:ℤ)) (2*N+1)
    push_cast at h
    unfold symmetricRatio
    apply (div_le_iff₀ (by positivity)).2
    calc
      _ ≤ ρ*(2*(N:ℝ)+1)+n := h
      _ = _ := by field_simp
  have hden : Tendsto (fun N : ℕ => 2*(N:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have herr : Tendsto (fun N : ℕ => (n:ℝ)/(2*(N:ℝ)+1)) atTop (nhds 0) :=
    hden.const_div_atTop (n:ℝ)
  have hlolim : Tendsto (fun N : ℕ => ρ-(n:ℝ)/(2*(N:ℝ)+1)) atTop (nhds ρ) := by
    simpa using tendsto_const_nhds.sub herr
  have huplim : Tendsto (fun N : ℕ => ρ+(n:ℝ)/(2*(N:ℝ)+1)) atTop (nhds ρ) := by
    simpa using tendsto_const_nhds.add herr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlolim huplim hlo hup

theorem upperDensity_eq_of_constant_blocks (A : Set ℤ) (n c : ℕ) (hn : 0 < n)
    (hc : ∀ x : ℤ, windowCount A x n = c) : upperDensity A = (c : ℝ) / n :=
  (symmetricRatio_tendsto_of_constant_blocks A n c hn hc).limsup_eq

end W01

#print axioms W01.windowCount_add_compl
#print axioms W01.symmetricRatio_tendsto_of_constant_blocks
#print axioms W01.upperDensity_eq_of_constant_blocks
