import W01.Basic
import W01.Density

/-! The parity consequence of saturation of the five-point path cliques. -/

open scoped BigOperators

namespace W01

attribute [local instance] Classical.propDecidable

noncomputable def member (A : Set ℤ) (z : ℤ) : ℕ := if z ∈ A then 1 else 0

theorem ordered_five_sum (f : ℤ → ℕ) (x₀ x₁ x₂ x₃ x₄ : ℤ)
    (h₀ : x₀ < x₁) (h₁ : x₁ < x₂) (h₂ : x₂ < x₃) (h₃ : x₃ < x₄) :
    (∑ x ∈ ({x₀, x₁, x₂, x₃, x₄} : Finset ℤ), f x) =
      f x₀ + f x₁ + f x₂ + f x₃ + f x₄ := by
  have hn₀ : x₀ ∉ ({x₁, x₂, x₃, x₄} : Finset ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hn₁ : x₁ ∉ ({x₂, x₃, x₄} : Finset ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hn₂ : x₂ ∉ ({x₃, x₄} : Finset ℤ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hn₃ : x₃ ∉ ({x₄} : Finset ℤ) := by
    simp only [Finset.mem_singleton]
    omega
  rw [Finset.sum_insert hn₀, Finset.sum_insert hn₁, Finset.sum_insert hn₂,
    Finset.sum_insert hn₃, Finset.sum_singleton]
  omega

theorem pathCount_aabb (A : Set ℤ) (a b t : ℤ) (ha : 0 < a) (hb : 0 < b) :
    pathCount A a b t 0 = member A t + member A (t+a) + member A (t+2*a) +
      member A (t+(2*a+b)) + member A (t+(2*a+2*b)) := by
  have hs := ordered_five_sum (fun x => member A (t+x))
    0 a (2*a) (2*a+b) (2*a+2*b) ha (by omega) (by omega) (by omega)
  unfold pathCount
  dsimp only [pathPoints]
  rw [Finset.card_filter]
  simpa only [member, add_zero] using hs

theorem pathCount_abba (A : Set ℤ) (a b t : ℤ) (ha : 0 < a) (hb : 0 < b) :
    pathCount A a b t 2 = member A t + member A (t+a) + member A (t+(a+b)) +
      member A (t+(a+2*b)) + member A (t+(2*a+2*b)) := by
  have hs := ordered_five_sum (fun x => member A (t+x))
    0 a (a+b) (a+2*b) (2*a+2*b) ha (by omega) (by omega) (by omega)
  unfold pathCount
  dsimp only [pathPoints]
  rw [Finset.card_filter]
  simpa only [member, add_zero] using hs

theorem pathCount_baba (A : Set ℤ) (a b t : ℤ) (ha : 0 < a) (hb : 0 < b) :
    pathCount A a b t 4 = member A t + member A (t+b) + member A (t+(a+b)) +
      member A (t+(a+2*b)) + member A (t+(2*a+2*b)) := by
  have hs := ordered_five_sum (fun x => member A (t+x))
    0 b (a+b) (a+2*b) (2*a+2*b) hb (by omega) (by omega) (by omega)
  unfold pathCount
  dsimp only [pathPoints]
  rw [Finset.card_filter]
  simpa only [member, add_zero] using hs

theorem saturated_abba_baba (A : Set ℤ) (a b t : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h₂ : pathCount A a b t 2 = 1) (h₄ : pathCount A a b t 4 = 1) :
    member A (t+a) = member A (t+b) := by
  rw [pathCount_abba A a b t ha hb] at h₂
  rw [pathCount_baba A a b t ha hb] at h₄
  omega

theorem windowCount_eq_sum_member (A : Set ℤ) (x : ℤ) (n : ℕ) :
    windowCount A x n = ∑ i ∈ Finset.range n, member A (x+(i:ℤ)) := rfl

theorem saturation_equal_windows (A : Set ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h₂ : ∀ u : ℕ, u < a → pathCount A a b u 2 = 1)
    (h₄ : ∀ u : ℕ, u < a → pathCount A a b u 4 = 1) :
    windowCount A a a = windowCount A b a := by
  simp only [windowCount_eq_sum_member]
  apply Finset.sum_congr rfl
  intro u hu
  have he := saturated_abba_baba A a b u (by exact_mod_cast ha)
    (by exact_mod_cast hb) (h₂ u (Finset.mem_range.mp hu)) (h₄ u (Finset.mem_range.mp hu))
  simpa only [add_comm] using he

theorem sum_pathCount_aabb (A : Set ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ u ∈ Finset.range b, pathCount A a b u 0) =
      windowCount A 0 b + windowCount A a b + windowCount A (2*(a:ℤ)) b +
      windowCount A (2*(a:ℤ)+b) b + windowCount A (2*(a:ℤ)+2*b) b := by
  calc
    _ = ∑ u ∈ Finset.range b,
        (member A (u:ℤ) + member A ((a:ℤ)+u) + member A (2*(a:ℤ)+u) +
        member A ((2*(a:ℤ)+b)+u) + member A ((2*(a:ℤ)+2*b)+u)) := by
      apply Finset.sum_congr rfl
      intro u hu
      simpa only [add_comm] using
        pathCount_aabb A a b u (by exact_mod_cast ha) (by exact_mod_cast hb)
    _ = _ := by simp only [Finset.sum_add_distrib, windowCount_eq_sum_member, zero_add]

theorem equality_parity_from_saturation (A : Set ℤ) (a b : ℕ)
    (hb : 0 < b) (hba : b < a)
    (h₀ : ∀ u : ℕ, u < b → pathCount A a b u 0 = 1)
    (h₂ : ∀ u : ℕ, u < a → pathCount A a b u 2 = 1)
    (h₄ : ∀ u : ℕ, u < a → pathCount A a b u 4 = 1) :
    ∃ t : ℕ, windowCount A 0 (2*a+3*b) = b+2*t := by
  have ha : 0 < a := by omega
  have hle : b ≤ a := by omega
  have heq := saturation_equal_windows A a b ha hb h₂ h₄
  have ha_split := windowCount_add A (a:ℤ) b (a-b)
  have hb_split := windowCount_add A (b:ℤ) (a-b) b
  have hlen : b+(a-b) = a := by omega
  have hlen' : (a-b)+b = a := by omega
  have hend : (b:ℤ)+((a-b:ℕ):ℤ) = a := by omega
  rw [hlen] at ha_split
  rw [hlen', hend] at hb_split
  have hgap : windowCount A (a+b:ℤ) (a-b) = windowCount A b (a-b) := by omega
  have hsat : (∑ u ∈ Finset.range b, pathCount A a b u 0) = b := by
    calc
      _ = ∑ _u ∈ Finset.range b, (1:ℕ) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact h₀ u (Finset.mem_range.mp hu)
      _ = b := by simp
  rw [sum_pathCount_aabb A a b ha hb] at hsat
  have hlast₂ := windowCount_add A (2*(a:ℤ)) b b
  have hlast₃ := windowCount_add A (2*(a:ℤ)) (2*b) b
  have hb₂ : b+b = 2*b := by omega
  have hb₃ : 2*b+b = 3*b := by omega
  rw [hb₂] at hlast₂
  rw [hb₃] at hlast₃
  have htwob : ((2*b:ℕ):ℤ) = 2*(b:ℤ) := by omega
  rw [htwob] at hlast₃
  have hblocks : windowCount A 0 b + windowCount A a b +
      windowCount A (2*(a:ℤ)) (3*b) = b := by omega
  have hfirst := windowCount_add A 0 b (a-b)
  rw [hlen, zero_add] at hfirst
  have hfirst₂ := windowCount_add A 0 a a
  have haa : a+a = 2*a := by omega
  rw [haa, zero_add] at hfirst₂
  have hall := windowCount_add A 0 (2*a) (3*b)
  have htwoa : ((2*a:ℕ):ℤ) = 2*(a:ℤ) := by omega
  rw [zero_add, htwoa] at hall
  exact ⟨windowCount A b (a-b), by omega⟩

theorem equality_counts_from_saturation (A : Set ℤ) (a b : ℕ)
    (hb : 0 < b) (hba : b < a)
    (h₀ : ∀ u : ℕ, u < b → pathCount A a b u 0 = 1)
    (h₂ : ∀ u : ℕ, u < a → pathCount A a b u 2 = 1)
    (h₄ : ∀ u : ℕ, u < a → pathCount A a b u 4 = 1)
    (heq : windowCount A 0 (2*a+3*b) + windowCount A 0 (3*a+2*b) = a+b) :
    ∃ t : ℕ, windowCount A 0 (2*a+3*b) = b+2*t ∧
      windowCount A 0 (3*a+2*b) + 2*t = a := by
  obtain ⟨t, ht⟩ := equality_parity_from_saturation A a b hb hba h₀ h₂ h₄
  exact ⟨t, ht, by omega⟩

theorem pathCount_shift (A : Set ℤ) (x a b t : ℤ) (w : Fin 6) :
    pathCount {z | z+x ∈ A} a b t w = pathCount A a b (x+t) w := by
  unfold pathCount
  congr 1
  apply Finset.filter_congr
  intro p hp
  change (t+p)+x ∈ A ↔ (x+t)+p ∈ A
  have he : (t+p)+x = (x+t)+p := by ring
  rw [he]

theorem windowCount_shift (A : Set ℤ) (x y : ℤ) (n : ℕ) :
    windowCount {z | z+x ∈ A} y n = windowCount A (x+y) n := by
  simp only [windowCount_eq_sum_member]
  apply Finset.sum_congr rfl
  intro i hi
  unfold member
  change (if (y+(i:ℤ))+x ∈ A then 1 else 0) =
    (if (x+y)+(i:ℤ) ∈ A then 1 else 0)
  have he : (y+(i:ℤ))+x = (x+y)+(i:ℤ) := by ring
  rw [he]

theorem equality_parity_at_from_saturation (A : Set ℤ) (a b : ℕ) (x : ℤ)
    (hb : 0 < b) (hba : b < a)
    (h₀ : ∀ u : ℕ, u < b → pathCount A a b (x+u) 0 = 1)
    (h₂ : ∀ u : ℕ, u < a → pathCount A a b (x+u) 2 = 1)
    (h₄ : ∀ u : ℕ, u < a → pathCount A a b (x+u) 4 = 1) :
    ∃ t : ℕ, windowCount A x (2*a+3*b) = b+2*t := by
  have h₀' : ∀ u : ℕ, u < b → pathCount {z | z+x ∈ A} a b u 0 = 1 := by
    intro u hu
    rw [pathCount_shift]
    exact h₀ u hu
  have h₂' : ∀ u : ℕ, u < a → pathCount {z | z+x ∈ A} a b u 2 = 1 := by
    intro u hu
    rw [pathCount_shift]
    exact h₂ u hu
  have h₄' : ∀ u : ℕ, u < a → pathCount {z | z+x ∈ A} a b u 4 = 1 := by
    intro u hu
    rw [pathCount_shift]
    exact h₄ u hu
  obtain ⟨t, ht⟩ := equality_parity_from_saturation {z | z+x ∈ A} a b hb hba h₀' h₂' h₄'
  rw [windowCount_shift, add_zero] at ht
  exact ⟨t, ht⟩

end W01

#print axioms W01.equality_parity_from_saturation
#print axioms W01.equality_counts_from_saturation
#print axioms W01.equality_parity_at_from_saturation
