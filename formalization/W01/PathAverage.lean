import W01.Equality

/-! The six-path averaging identity and its saturation consequence, for every
pair of positive natural parameters and every subset of the integers. -/

open scoped BigOperators

namespace W01

attribute [local instance] Classical.propDecidable

def pathLast (a b : ℕ) (w : Fin 6) : ℕ :=
  if w.val = 0 ∨ w.val = 1 ∨ w.val = 3 then b else a

noncomputable def pathSum (A : Set ℤ) (a b : ℕ) (x : ℤ) (w : Fin 6) : ℕ :=
  ∑ u ∈ Finset.range (pathLast a b w), pathCount A a b (x+(u:ℤ)) w

theorem pathSum_eq_windowSum (A : Set ℤ) (a b : ℕ) (x : ℤ) (w : Fin 6) :
    pathSum A a b x w =
      ∑ p ∈ pathPoints a b w, windowCount A (x+p) (pathLast a b w) := by
  classical
  unfold pathSum pathCount windowCount
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro u hu
  congr 2
  ring

noncomputable def pathFormula (A : Set ℤ) (a b : ℕ) (x : ℤ) (w : Fin 6) : ℕ :=
  let C := fun (s : ℤ) (n : ℕ) => windowCount A (x+s) n
  match w.val with
  | 0 => C 0 b + C a b + C (2*a) b + C (2*a+b) b + C (2*a+2*b) b
  | 1 => C 0 b + C a b + C (a+b) b + C (2*a+b) b + C (2*a+2*b) b
  | 2 => C 0 a + C a a + C (a+b) a + C (a+2*b) a + C (2*a+2*b) a
  | 3 => C 0 b + C b b + C (a+b) b + C (2*a+b) b + C (2*a+2*b) b
  | 4 => C 0 a + C b a + C (a+b) a + C (a+2*b) a + C (2*a+2*b) a
  | _ => C 0 a + C b a + C (2*b) a + C (a+2*b) a + C (2*a+2*b) a

theorem pathSum_eq_formula (A : Set ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (x : ℤ) (w : Fin 6) : pathSum A a b x w = pathFormula A a b x w := by
  have ha' : (0:ℤ) < a := by exact_mod_cast ha
  have hb' : (0:ℤ) < b := by exact_mod_cast hb
  rw [pathSum_eq_windowSum]
  fin_cases w <;> dsimp [pathPoints, pathLast, pathFormula] <;>
    apply ordered_five_sum <;> omega

/-- The identity is an exact finite-sum equality, with no avoidance assumption. -/
theorem path_average_identity (A : Set ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (x : ℤ) :
    pathSum A a b x 0 + pathSum A a b x 1 + pathSum A a b x 2 +
      pathSum A a b x 3 + pathSum A a b x 4 + pathSum A a b x 5 =
      3 * (windowCount A x (2*a+3*b) + windowCount A x (3*a+2*b)) := by
  simp only [pathSum_eq_formula A a b ha hb x]
  dsimp [pathFormula]
  have hab := windowCount_add A x a b
  have haa := windowCount_add A x a a
  have hba := windowCount_add A x b a
  have hbb := windowCount_add A x b b
  have h2ab := windowCount_add A x (2*a) b
  have h2ba := windowCount_add A x (2*b) a
  have haba := windowCount_add A x (a+b) a
  have habb := windowCount_add A x (a+b) b
  have h2abb := windowCount_add A x (2*a+b) b
  have ha2ba := windowCount_add A x (a+2*b) a
  have h2a2ba := windowCount_add A x (2*a+2*b) a
  have h2a2bb := windowCount_add A x (2*a+2*b) b
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_zero] at *
  have h1 : a+a = 2*a := by omega
  have h2 : b+b = 2*b := by omega
  have h3 : b+a = a+b := by omega
  have h4 : 2*b+a = a+2*b := by omega
  have h5 : a+b+a = 2*a+b := by omega
  have h6 : a+b+b = a+2*b := by omega
  have h7 : 2*a+b+b = 2*a+2*b := by omega
  have h8 : a+2*b+a = 2*a+2*b := by omega
  have h9 : 2*a+2*b+a = 3*a+2*b := by omega
  have h10 : 2*a+2*b+b = 2*a+3*b := by omega
  rw [h1] at haa
  rw [h2] at hbb
  rw [h3] at hba
  rw [h4] at h2ba
  rw [h5] at haba
  rw [h6] at habb
  rw [h7] at h2abb
  rw [h8] at ha2ba
  rw [h9] at h2a2ba
  rw [h10] at h2a2bb
  omega

theorem pathSum_le_last (A : Set ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : Avoids a b A) (x : ℤ) (w : Fin 6) :
    pathSum A a b x w ≤ pathLast a b w := by
  unfold pathSum
  calc
    _ ≤ ∑ _u ∈ Finset.range (pathLast a b w), (1:ℕ) := by
      apply Finset.sum_le_sum
      intro u hu
      exact pathCount_le_one a b (by exact_mod_cast ha) (by exact_mod_cast hb) A hA _ w
    _ = _ := by simp

theorem weighted_window_bound (A : Set ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : Avoids a b A) (x : ℤ) :
    windowCount A x (2*a+3*b) + windowCount A x (3*a+2*b) ≤ a+b := by
  have hid := path_average_identity A a b ha hb x
  have h0 := pathSum_le_last A a b ha hb hA x 0
  have h1 := pathSum_le_last A a b ha hb hA x 1
  have h2 := pathSum_le_last A a b ha hb hA x 2
  have h3 := pathSum_le_last A a b ha hb hA x 3
  have h4 := pathSum_le_last A a b ha hb hA x 4
  have h5 := pathSum_le_last A a b ha hb hA x 5
  change pathSum A a b x 0 ≤ b at h0
  change pathSum A a b x 1 ≤ b at h1
  change pathSum A a b x 2 ≤ a at h2
  change pathSum A a b x 3 ≤ b at h3
  change pathSum A a b x 4 ≤ a at h4
  change pathSum A a b x 5 ≤ a at h5
  omega

theorem equality_pathSum (A : Set ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : Avoids a b A) (x : ℤ)
    (heq : windowCount A x (2*a+3*b) + windowCount A x (3*a+2*b) = a+b)
    (w : Fin 6) : pathSum A a b x w = pathLast a b w := by
  have hid := path_average_identity A a b ha hb x
  rw [heq] at hid
  have h0 := pathSum_le_last A a b ha hb hA x 0
  have h1 := pathSum_le_last A a b ha hb hA x 1
  have h2 := pathSum_le_last A a b ha hb hA x 2
  have h3 := pathSum_le_last A a b ha hb hA x 3
  have h4 := pathSum_le_last A a b ha hb hA x 4
  have h5 := pathSum_le_last A a b ha hb hA x 5
  change pathSum A a b x 0 ≤ b at h0
  change pathSum A a b x 1 ≤ b at h1
  change pathSum A a b x 2 ≤ a at h2
  change pathSum A a b x 3 ≤ b at h3
  change pathSum A a b x 4 ≤ a at h4
  change pathSum A a b x 5 ≤ a at h5
  have e0 : pathSum A a b x 0 = b := by omega
  have e1 : pathSum A a b x 1 = b := by omega
  have e2 : pathSum A a b x 2 = a := by omega
  have e3 : pathSum A a b x 3 = b := by omega
  have e4 : pathSum A a b x 4 = a := by omega
  have e5 : pathSum A a b x 5 = a := by omega
  fin_cases w
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact e5

theorem equality_path_saturation (A : Set ℤ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : Avoids a b A) (x : ℤ)
    (heq : windowCount A x (2*a+3*b) + windowCount A x (3*a+2*b) = a+b)
    (w : Fin 6) (u : ℕ) (hu : u < pathLast a b w) :
    pathCount A a b (x+(u:ℤ)) w = 1 := by
  have hsum := equality_pathSum A a b ha hb hA x heq w
  have hle (v : ℕ) : pathCount A a b (x+(v:ℤ)) w ≤ 1 :=
    pathCount_le_one a b (by exact_mod_cast ha) (by exact_mod_cast hb) A hA _ w
  by_contra hne
  have hlt : pathCount A a b (x+(u:ℤ)) w < 1 := by have := hle u; omega
  have hstrict := Finset.sum_lt_sum (fun v (_ : v ∈ Finset.range (pathLast a b w)) => hle v)
    ⟨u, Finset.mem_range.mpr hu, hlt⟩
  have hbad : pathSum A a b x w < pathLast a b w := by simpa [pathSum] using hstrict
  omega

theorem equality_parity (A : Set ℤ) (a b : ℕ) (hb : 0 < b) (hba : b < a)
    (hA : Avoids a b A)
    (heq : windowCount A 0 (2*a+3*b) + windowCount A 0 (3*a+2*b) = a+b) :
    ∃ t : ℕ, windowCount A 0 (2*a+3*b) = b+2*t ∧
      windowCount A 0 (3*a+2*b) = a-2*t := by
  have ha : 0 < a := by omega
  have hsat := equality_path_saturation A a b ha hb hA 0 heq
  have h₀ (u : ℕ) (hu : u < b) : pathCount A a b u 0 = 1 := by
    simpa only [zero_add] using hsat 0 u (by simpa [pathLast] using hu)
  have h₂ (u : ℕ) (hu : u < a) : pathCount A a b u 2 = 1 := by
    simpa only [zero_add] using hsat 2 u (by simpa [pathLast] using hu)
  have h₄ (u : ℕ) (hu : u < a) : pathCount A a b u 4 = 1 := by
    simpa only [zero_add] using hsat 4 u (by simpa [pathLast] using hu)
  obtain ⟨t, ht⟩ := equality_parity_from_saturation A a b hb hba h₀ h₂ h₄
  exact ⟨t, ht, by omega⟩

end W01

#print axioms W01.path_average_identity
#print axioms W01.weighted_window_bound
#print axioms W01.equality_path_saturation
#print axioms W01.equality_parity
