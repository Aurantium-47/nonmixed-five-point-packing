import W01.Lower
import W01.PeriodicDensity

/-! Exact counting of the periodic lower construction in every full-period window. -/

namespace W01

open Filter

theorem lower_windowCount
    (a b q r : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q+r)
    (hr : r = 1 ∨ r = 2) :
    ∀ x : ℤ, windowCount (lowerCenters a b q) x (2*a+3*b).toNat =
      (b+2*q).toNat := by
  classical
  intro x
  let n : ℤ := 2*a+3*b
  let c : ℤ := b+2*q
  let g : ℤ := a-b
  have hn : 0 < n := by dsimp [n]; omega
  have hc : 0 < c := by dsimp [c]; rcases hr with rfl | rfl <;> omega
  have hncast : (n.toNat : ℤ) = n := by omega
  let f : ℤ → ℤ := fun t => x+(t*g-x)%n
  have frep (t : ℤ) : f t = t*g+(-((t*g-x)/n))*n := by
    dsimp [f]
    have he := Int.emod_add_ediv (t*g-x) n
    nlinarith [he]
  change windowCount (lowerCenters a b q) x n.toNat = c.toNat
  rw [windowCount_eq_interval_card, hncast]
  calc
    ((Finset.Ico x (x+n)).filter (· ∈ lowerCenters a b q)).card =
        (Finset.Ico 0 c).card := by
      symm
      apply Finset.card_bij (fun (t : ℤ) _ => f t)
      · intro t ht
        obtain ⟨ht0, htc⟩ := Finset.mem_Ico.mp ht
        have hm0 := Int.emod_nonneg (t*g-x) (ne_of_gt hn)
        have hmn := Int.emod_lt_of_pos (t*g-x) hn
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_Ico.mpr
          dsimp [f]
          omega
        · exact ⟨t, -((t*g-x)/n), ht0, htc, frep t⟩
      · intro s hs t ht hst
        obtain ⟨hs0, hsc⟩ := Finset.mem_Ico.mp hs
        obtain ⟨ht0, htc⟩ := Finset.mem_Ico.mp ht
        have heq : s*(a-b)+(-((s*g-x)/n))*(2*a+3*b) =
            t*(a-b)+(-((t*g-x)/n))*(2*a+3*b) := by
          change s*g+(-((s*g-x)/n))*n = t*g+(-((t*g-x)/n))*n
          rw [← frep s, ← frep t]
          exact hst
        exact (lower_representation_unique a b q r s t
          (-((s*g-x)/n)) (-((t*g-x)/n)) ha hcop hdiv hr hc
          hs0 hsc ht0 htc heq).1
      · intro y hy
        obtain ⟨hyI, hyA⟩ := Finset.mem_filter.mp hy
        obtain ⟨hy0, hyn⟩ := Finset.mem_Ico.mp hyI
        obtain ⟨t, z, ht0, htc, he⟩ := hyA
        refine ⟨t, Finset.mem_Ico.mpr ⟨ht0, htc⟩, ?_⟩
        have hmod : (y-x)%n = (t*g-x)%n := by
          calc
            (y-x)%n = ((t*g-x)+z*n)%n := by
              congr 1
              dsimp [g, n]
              nlinarith [he]
            _ = (t*g-x)%n := by rw [Int.add_mul_emod_self]
        have hrem : (y-x)%n = y-x :=
          Int.emod_eq_of_lt (by omega : 0 ≤ y-x) (by omega : y-x < n)
        dsimp [f]
        rw [← hmod, hrem]
        omega
    _ = c.toNat := by rw [Int.card_Ico]; simp

theorem lower_swapped_windowCount
    (a b q r : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q+r)
    (hr : r = 3 ∨ r = 4) :
    ∀ x : ℤ, windowCount (lowerCenters b a (-q-1)) x (3*a+2*b).toNat =
      (a-2*(q+1)).toNat := by
  intro x
  have hs : b-a = 5*(-q-1)+(5-r) := by omega
  have hrs : 5-r = 1 ∨ 5-r = 2 := by omega
  have h := lower_windowCount b a (-q-1) (5-r) hb ha hcop.symm hs hrs x
  have hn : 3*a+2*b = 2*b+3*a := by ring
  have hc : a-2*(q+1) = a+2*(-q-1) := by ring
  rw [hn, hc]
  exact h

theorem lower_symmetricRatio_tendsto
    (a b q r : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q+r)
    (hr : r = 1 ∨ r = 2) :
    Tendsto (symmetricRatio (lowerCenters a b q)) atTop
      (nhds (((b+2*q : ℤ) : ℝ) / ((2*a+3*b : ℤ) : ℝ))) := by
  have hn : 0 < 2*a+3*b := by omega
  have hc : 0 < b+2*q := by rcases hr with rfl | rfl <;> omega
  have h := symmetricRatio_tendsto_of_constant_blocks (lowerCenters a b q)
    (2*a+3*b).toNat (b+2*q).toNat (by omega)
    (lower_windowCount a b q r ha hb hcop hdiv hr)
  have hncast : ((2*a+3*b).toNat : ℝ) = ((2*a+3*b : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hn.le)
  have hccast : ((b+2*q).toNat : ℝ) = ((b+2*q : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hc.le)
  simpa only [hncast, hccast] using h

theorem lower_upperDensity
    (a b q r : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q+r)
    (hr : r = 1 ∨ r = 2) :
    upperDensity (lowerCenters a b q) =
      ((b+2*q : ℤ) : ℝ) / ((2*a+3*b : ℤ) : ℝ) :=
  (lower_symmetricRatio_tendsto a b q r ha hb hcop hdiv hr).limsup_eq

theorem lower_swapped_symmetricRatio_tendsto
    (a b q r : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q+r)
    (hr : r = 3 ∨ r = 4) :
    Tendsto (symmetricRatio (lowerCenters b a (-q-1))) atTop
      (nhds (((a-2*(q+1) : ℤ) : ℝ) / ((3*a+2*b : ℤ) : ℝ))) := by
  have hs : b-a = 5*(-q-1)+(5-r) := by omega
  have hrs : 5-r = 1 ∨ 5-r = 2 := by omega
  have h := lower_symmetricRatio_tendsto b a (-q-1) (5-r)
    hb ha hcop.symm hs hrs
  have hn : 2*b+3*a = 3*a+2*b := by ring
  have hc : a+2*(-q-1) = a-2*(q+1) := by ring
  simpa only [hn, hc] using h

theorem lower_swapped_upperDensity
    (a b q r : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (hdiv : a-b = 5*q+r)
    (hr : r = 3 ∨ r = 4) :
    upperDensity (lowerCenters b a (-q-1)) =
      ((a-2*(q+1) : ℤ) : ℝ) / ((3*a+2*b : ℤ) : ℝ) :=
  (lower_swapped_symmetricRatio_tendsto a b q r ha hb hcop hdiv hr).limsup_eq

end W01

#print axioms W01.lower_windowCount
#print axioms W01.lower_swapped_windowCount
#print axioms W01.lower_symmetricRatio_tendsto
#print axioms W01.lower_upperDensity
#print axioms W01.lower_swapped_symmetricRatio_tendsto
#print axioms W01.lower_swapped_upperDensity
