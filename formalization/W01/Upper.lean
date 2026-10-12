import W01.PathAverage
import W01.Arithmetic

namespace W01

theorem equality_parity_at (A : Set ℤ) (a b : ℕ) (x : ℤ)
    (hb : 0 < b) (hba : b < a) (hA : Avoids a b A)
    (heq : windowCount A x (2*a+3*b) + windowCount A x (3*a+2*b) = a+b) :
    ∃ t : ℕ, windowCount A x (2*a+3*b) = b+2*t := by
  have ha : 0 < a := by omega
  have hsat := equality_path_saturation A a b ha hb hA x heq
  apply equality_parity_at_from_saturation A a b x hb hba
  · intro u hu
    exact hsat 0 u (by simpa [pathLast] using hu)
  · intro u hu
    exact hsat 2 u (by simpa [pathLast] using hu)
  · intro u hu
    exact hsat 4 u (by simpa [pathLast] using hu)

noncomputable def smallRho (a b : ℕ) (q : ℤ) : ℝ :=
  ((b : ℝ)+2*(q:ℝ))/(2*(a:ℝ)+3*(b:ℝ))

noncomputable def largeRho (a b : ℕ) (q : ℤ) : ℝ :=
  ((a : ℝ)-2*((q:ℝ)+1))/(3*(a:ℝ)+2*(b:ℝ))

theorem small_upper (A : Set ℤ) (a b : ℕ) (q r : ℤ)
    (hb : 0 < b) (hba : b < a) (hA : Avoids a b A)
    (hdiv : (a:ℤ)-b = 5*q+r) (hr : r=1 ∨ r=2) :
    upperDensity A ≤ smallRho a b q := by
  have ha : 0 < a := by omega
  have hnum : (0:ℝ) < (b:ℝ)+2*(q:ℝ) := by
    exact_mod_cast small_numerator_positive (a:ℤ) b q r (by omega) (by omega) hdiv hr
  have hρ : 0 ≤ smallRho a b q := by unfold smallRho; positivity
  apply upperDensity_le_of_good_blocks A (smallRho a b q) (3*a+2*b) hρ
  intro x
  have hs : (windowCount A x (2*a+3*b):ℤ) + windowCount A x (3*a+2*b) ≤ (a:ℤ)+b := by
    exact_mod_cast weighted_window_bound A a b ha hb hA x
  have he : (windowCount A x (2*a+3*b):ℤ) + windowCount A x (3*a+2*b) = (a:ℤ)+b →
      ∃ t : ℤ, (windowCount A x (2*a+3*b):ℤ) = (b:ℤ)+2*t := by
    intro he
    have he' : windowCount A x (2*a+3*b) + windowCount A x (3*a+2*b) = a+b := by exact_mod_cast he
    obtain ⟨t, ht⟩ := equality_parity_at A a b x hb hba hA he'
    exact ⟨t, by exact_mod_cast ht⟩
  have hchoice := small_local_real (a:ℤ) b q r (windowCount A x (2*a+3*b))
    (windowCount A x (3*a+2*b)) (by omega) (by omega) hdiv hr hs he
  push_cast at hchoice
  rcases hchoice with hc | hc
  · refine ⟨2*a+3*b, by omega, by omega, ?_⟩
    simpa [smallRho] using hc
  · refine ⟨3*a+2*b, by omega, le_rfl, ?_⟩
    simpa [smallRho] using hc

theorem large_upper (A : Set ℤ) (a b : ℕ) (q r : ℤ)
    (hb : 0 < b) (hba : b < a) (hA : Avoids a b A)
    (hdiv : (a:ℤ)-b = 5*q+r) (hr : r=3 ∨ r=4) :
    upperDensity A ≤ largeRho a b q := by
  have ha : 0 < a := by omega
  have hq : 0 ≤ q := by omega
  have hnum : (0:ℝ) < (a:ℝ)-2*((q:ℝ)+1) := by
    exact_mod_cast (show (0:ℤ) < (a:ℤ)-2*(q+1) by omega)
  have hρ : 0 ≤ largeRho a b q := by unfold largeRho; positivity
  apply upperDensity_le_of_good_blocks A (largeRho a b q) (3*a+2*b) hρ
  intro x
  have hs : (windowCount A x (2*a+3*b):ℤ) + windowCount A x (3*a+2*b) ≤ (a:ℤ)+b := by
    exact_mod_cast weighted_window_bound A a b ha hb hA x
  have he : (windowCount A x (2*a+3*b):ℤ) + windowCount A x (3*a+2*b) = (a:ℤ)+b →
      ∃ t : ℤ, (windowCount A x (2*a+3*b):ℤ) = (b:ℤ)+2*t := by
    intro he
    have he' : windowCount A x (2*a+3*b) + windowCount A x (3*a+2*b) = a+b := by exact_mod_cast he
    obtain ⟨t, ht⟩ := equality_parity_at A a b x hb hba hA he'
    exact ⟨t, by exact_mod_cast ht⟩
  have hchoice := large_local_real (a:ℤ) b q r (windowCount A x (2*a+3*b))
    (windowCount A x (3*a+2*b)) (by omega) (by omega) hdiv hr hs he
  push_cast at hchoice
  rcases hchoice with hc | hc
  · refine ⟨2*a+3*b, by omega, by omega, ?_⟩
    simpa [largeRho] using hc
  · refine ⟨3*a+2*b, by omega, le_rfl, ?_⟩
    simpa [largeRho] using hc

/-- The volume bound follows already from the path average, without coprimality. -/
theorem fifth_upper (A : Set ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : Avoids a b A) : upperDensity A ≤ (1:ℝ)/5 := by
  apply upperDensity_le_of_good_blocks A ((1:ℝ)/5) (3*(a+b)) (by norm_num)
  intro x
  have hs : (windowCount A x (2*a+3*b):ℝ) + windowCount A x (3*a+2*b) ≤ (a:ℝ)+b := by
    exact_mod_cast weighted_window_bound A a b ha hb hA x
  by_cases hc : (windowCount A x (2*a+3*b):ℝ) ≤ (1:ℝ)/5 * (2*a+3*b:ℕ)
  · exact ⟨2*a+3*b, by omega, by omega, hc⟩
  · refine ⟨3*a+2*b, by omega, by omega, ?_⟩
    push_cast at *
    linarith

noncomputable def targetDensity (a b : ℕ) (q r : ℤ) : ℝ :=
  if r = 0 then 1/5 else if r = 1 ∨ r = 2 then smallRho a b q else largeRho a b q

theorem smallRho_swap (a b : ℕ) (q : ℤ) : smallRho b a (-q-1) = largeRho a b q := by
  unfold smallRho largeRho
  push_cast
  congr 1 <;> ring

/-- All positive parameters, all three branches, and arbitrary packing center sets. -/
theorem packing_upper_bound (A : Set ℤ) (a b : ℕ) (q r : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hA : IsPacking a b A)
    (hdiv : (a:ℤ)-b = 5*q+r) (hr0 : 0 ≤ r) (hr5 : r < 5) :
    upperDensity A ≤ targetDensity a b q r := by
  have hav := (packing_iff_avoids (a:ℤ) b (by omega) (by omega) A).mp hA
  by_cases hr : r = 0
  · simpa [targetDensity, hr] using fifth_upper A a b ha hb hav
  have hab : a ≠ b := by intro he; subst b; omega
  rcases lt_or_gt_of_ne hab with hab | hba
  · have hav' := (avoids_comm (a:ℤ) b A).mp hav
    have hd' : (b:ℤ)-a = 5*(-q-1)+(5-r) := by omega
    interval_cases r
    all_goals norm_num [targetDensity] at *
    · have hu := large_upper A b a (-q-1) 4 ha hab hav' hd' (by omega)
      simpa [smallRho, largeRho, mul_comm, add_comm, add_left_comm, add_assoc] using hu
    · have hu := large_upper A b a (-q-1) 3 ha hab hav' hd' (by omega)
      simpa [smallRho, largeRho, mul_comm, add_comm, add_left_comm, add_assoc] using hu
    · have hu := small_upper A b a (-q-1) 2 ha hab hav' hd' (by omega)
      rwa [smallRho_swap] at hu
    · have hu := small_upper A b a (-q-1) 1 ha hab hav' hd' (by omega)
      rwa [smallRho_swap] at hu
  · interval_cases r
    all_goals norm_num [targetDensity] at *
    · exact small_upper A a b q 1 hb hba hav hdiv (by omega)
    · exact small_upper A a b q 2 hb hba hav hdiv (by omega)
    · exact large_upper A a b q 3 hb hba hav hdiv (by omega)
    · exact large_upper A a b q 4 hb hba hav hdiv (by omega)

end W01

#print axioms W01.equality_parity_at
#print axioms W01.small_upper
#print axioms W01.large_upper
#print axioms W01.fifth_upper
#print axioms W01.packing_upper_bound
