import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Disjoint
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Basic integer objects for the five-point nonmixed-gap packing problem. -/

namespace W01

def shape (a b : ℤ) : Finset ℤ := {0, a, 2*a, 2*a+b, 2*a+2*b}

def forbidden (a b : ℤ) : Finset ℤ :=
  {a, 2*a, b, 2*b, a+b, 2*a+b, a+2*b, 2*a+2*b}

def translate (x : ℤ) (S : Finset ℤ) : Set ℤ :=
  {z | ∃ s ∈ S, z = x + s}

def IsPacking (a b : ℤ) (A : Set ℤ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
    Disjoint (translate x (shape a b)) (translate y (shape a b))

def Avoids (a b : ℤ) (A : Set ℤ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x < y → y-x ∉ forbidden a b

theorem mem_forbidden_iff (a b d : ℤ) :
    d ∈ forbidden a b ↔
      d = a ∨ d = 2*a ∨ d = b ∨ d = 2*b ∨ d = a+b ∨
      d = 2*a+b ∨ d = a+2*b ∨ d = 2*a+2*b := by
  simp [forbidden]

theorem mem_shape_iff (a b s : ℤ) :
    s ∈ shape a b ↔ s = 0 ∨ s = a ∨ s = 2*a ∨
      s = 2*a+b ∨ s = 2*a+2*b := by
  simp [shape]

theorem positive_differences (a b d : ℤ) (ha : 0 < a) (hb : 0 < b) :
    d ∈ forbidden a b ↔
      ∃ u ∈ shape a b, ∃ v ∈ shape a b, u < v ∧ v-u = d := by
  constructor
  · intro hd
    rw [mem_forbidden_iff] at hd
    rcases hd with (hd | hd | hd | hd | hd | hd | hd | hd) <;> subst d
    · exact ⟨0, by simp [shape], a, by simp [shape], ha, by ring⟩
    · exact ⟨0, by simp [shape], 2*a, by simp [shape], by omega, by ring⟩
    · exact ⟨2*a, by simp [shape], 2*a+b, by simp [shape], by omega, by ring⟩
    · exact ⟨2*a, by simp [shape], 2*a+2*b, by simp [shape], by omega, by ring⟩
    · exact ⟨a, by simp [shape], 2*a+b, by simp [shape], by omega, by ring⟩
    · exact ⟨0, by simp [shape], 2*a+b, by simp [shape], by omega, by ring⟩
    · exact ⟨a, by simp [shape], 2*a+2*b, by simp [shape], by omega, by ring⟩
    · exact ⟨0, by simp [shape], 2*a+2*b, by simp [shape], by omega, by ring⟩
  · rintro ⟨u, hu, v, hv, huv, hd⟩
    rw [mem_shape_iff] at hu hv
    rw [mem_forbidden_iff]
    rcases hu with (hu | hu | hu | hu | hu) <;> subst u <;>
      rcases hv with (hv | hv | hv | hv | hv) <;> subst v <;> omega

theorem forbidden_pos (a b d : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hd : d ∈ forbidden a b) : 0 < d := by
  rw [mem_forbidden_iff] at hd
  rcases hd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega

theorem forbidden_coefficients (a b d : ℤ) :
    d ∈ forbidden a b ↔
      ∃ i j : ℤ, 0 ≤ i ∧ i ≤ 2 ∧ 0 ≤ j ∧ j ≤ 2 ∧
        0 < i+j ∧ d = i*a+j*b := by
  constructor
  · intro hd
    rw [mem_forbidden_iff] at hd
    rcases hd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1, 0, by norm_num⟩
    · exact ⟨2, 0, by norm_num⟩
    · exact ⟨0, 1, by norm_num⟩
    · exact ⟨0, 2, by norm_num⟩
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨2, 1, by norm_num⟩
    · exact ⟨1, 2, by norm_num⟩
    · exact ⟨2, 2, by norm_num⟩
  · rintro ⟨i, j, hi0, hi2, hj0, hj2, hij, rfl⟩
    interval_cases i <;> interval_cases j <;>
      simp_all [forbidden]

theorem forbidden_comm (a b : ℤ) : forbidden a b = forbidden b a := by
  ext d
  simp only [mem_forbidden_iff]
  omega

theorem ordered_five_card (x₀ x₁ x₂ x₃ x₄ : ℤ)
    (h₀ : x₀ < x₁) (h₁ : x₁ < x₂) (h₂ : x₂ < x₃) (h₃ : x₃ < x₄) :
    ({x₀, x₁, x₂, x₃, x₄} : Finset ℤ).card = 5 := by
  have hn₀ : ¬ (x₀ = x₁ ∨ x₀ = x₂ ∨ x₀ = x₃ ∨ x₀ = x₄) := by omega
  have hn₁ : ¬ (x₁ = x₂ ∨ x₁ = x₃ ∨ x₁ = x₄) := by omega
  have hn₂ : ¬ (x₂ = x₃ ∨ x₂ = x₄) := by omega
  have hn₃ : x₃ ≠ x₄ := by omega
  simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton,
    Finset.card_singleton, hn₀, hn₁, hn₂, hn₃, if_false]

theorem shape_card (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (shape a b).card = 5 := by
  apply ordered_five_card <;> omega

theorem packing_iff_avoids (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (A : Set ℤ) : IsPacking a b A ↔ Avoids a b A := by
  constructor
  · intro hp x hx y hy hxy hd
    obtain ⟨u, hu, v, hv, huv, hd⟩ := (positive_differences a b (y-x) ha hb).mp hd
    have hdisj := hp x hx y hy (by omega)
    have hcommon : x+v ∈ translate y (shape a b) := by
      exact ⟨u, hu, by omega⟩
    exact (Set.disjoint_left.mp hdisj) ⟨v, hv, rfl⟩ hcommon
  · intro hav x hx y hy hxy
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, hzu⟩ ⟨v, hv, hzv⟩
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have hd : y-x ∈ forbidden a b := by
        apply (positive_differences a b (y-x) ha hb).mpr
        exact ⟨v, hv, u, hu, by omega, by omega⟩
      exact hav x hx y hy hlt hd
    · have hd : x-y ∈ forbidden a b := by
        apply (positive_differences a b (x-y) ha hb).mpr
        exact ⟨u, hu, v, hv, by omega, by omega⟩
      exact hav y hy x hx hgt hd

theorem avoids_comm (a b : ℤ) (A : Set ℤ) : Avoids a b A ↔ Avoids b a A := by
  unfold Avoids
  rw [forbidden_comm]

theorem avoids_shift (a b t : ℤ) (A : Set ℤ) (hA : Avoids a b A) :
    Avoids a b {x | x+t ∈ A} := by
  intro x hx y hy hxy hd
  have hh := hA (x+t) hx (y+t) hy (by omega)
  have he : (y+t)-(x+t) = y-x := by ring
  exact hh (he ▸ hd)

def pathPoints (a b : ℤ) (w : Fin 6) : Finset ℤ :=
  match w.val with
  | 0 => {0, a, 2*a, 2*a+b, 2*a+2*b}
  | 1 => {0, a, a+b, 2*a+b, 2*a+2*b}
  | 2 => {0, a, a+b, a+2*b, 2*a+2*b}
  | 3 => {0, b, a+b, 2*a+b, 2*a+2*b}
  | 4 => {0, b, a+b, a+2*b, 2*a+2*b}
  | _ => {0, b, 2*b, a+2*b, 2*a+2*b}

theorem path_card (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (w : Fin 6) :
    (pathPoints a b w).card = 5 := by
  fin_cases w <;> dsimp [pathPoints] <;> apply ordered_five_card <;> omega

theorem path_clique (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (w : Fin 6) (u v : ℤ) (hu : u ∈ pathPoints a b w)
    (hv : v ∈ pathPoints a b w) (huv : u < v) :
    v-u ∈ forbidden a b := by
  rw [mem_forbidden_iff]
  fin_cases w <;> simp only [pathPoints, Finset.mem_insert, Finset.mem_singleton] at hu hv <;>
    rcases hu with (hu | hu | hu | hu | hu) <;> subst u <;>
    rcases hv with (hv | hv | hv | hv | hv) <;> subst v <;> omega

theorem path_inter_subsingleton (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (A : Set ℤ) (hA : Avoids a b A) (t : ℤ) (w : Fin 6) :
    (A ∩ translate t (pathPoints a b w)).Subsingleton := by
  rintro x ⟨hx, u, hu, hxu⟩ y ⟨hy, v, hv, hyv⟩
  rcases lt_trichotomy u v with huv | huv | huv
  · have hdiff := path_clique a b ha hb w u v hu hv huv
    have hbad := hA x hx y hy (by omega)
    exfalso
    apply hbad
    convert hdiff using 1
    omega
  · omega
  · have hdiff := path_clique a b ha hb w v u hv hu huv
    have hbad := hA y hy x hx (by omega)
    exfalso
    apply hbad
    convert hdiff using 1
    omega

noncomputable def pathCount (A : Set ℤ) (a b t : ℤ) (w : Fin 6) : ℕ := by
  classical
  exact ((pathPoints a b w).filter (fun p => t+p ∈ A)).card

theorem pathCount_le_one (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (A : Set ℤ) (hA : Avoids a b A) (t : ℤ) (w : Fin 6) :
    pathCount A a b t w ≤ 1 := by
  classical
  unfold pathCount
  rw [Finset.card_le_one]
  intro u hu v hv
  obtain ⟨hu, hAu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hv, hAv⟩ := Finset.mem_filter.mp hv
  have he := path_inter_subsingleton a b ha hb A hA t w
    ⟨hAu, u, hu, rfl⟩ ⟨hAv, v, hv, rfl⟩
  omega

end W01

#print axioms W01.positive_differences
#print axioms W01.forbidden_coefficients
#print axioms W01.packing_iff_avoids
#print axioms W01.shape_card
#print axioms W01.path_card
#print axioms W01.pathCount_le_one
