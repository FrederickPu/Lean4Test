import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem kevin {a b c : ℝ} : a ≥ 0 → c > 0 → b*a = c → b > 0 := by
  intros ha hc h
  apply by_contradiction
  intro hb
  simp at hb
  have han : a ≠ 0 := by {
    intro q
    simp [q] at h
    linarith
  }
  have hbn : b ≠ 0 := by {
    intro q
    simp [q] at h
    linarith
  }
  have : a > 0 := by exact Ne.lt_of_le (id (Ne.symm han)) ha
  have : a*b < 0 := by exact Linarith.mul_neg (Ne.lt_of_le hbn hb) this
  linarith

theorem kevin1 {a b c : ℝ} : a > 0 → c ≥ 0 → b*a = c → b ≥ 0 := by
  intros ha hc h
  have : a ≠ 0 := by linarith
  apply by_contradiction
  intro hb
  simp at hb
  have : b*a < 0 := by exact mul_neg_of_neg_of_pos hb ha
  linarith

theorem F_zero_iff (α β x y : ℝ) (ha : α > 0) (hb : β > 0) (h : α*x^2 + β*y^2 = (x^2 + y^2)^2) : 2*x^2*y+2*y^3 - β*y = 0 ↔ (x, y) ∈ ({(0, 0), (α.sqrt, 0), (-α.sqrt, 0)} : Set (ℝ × ℝ)) ∪ {p : ℝ × ℝ | (β - α)*p.fst^2 = β^2 / 4 ∧ (β - α)*p.snd^2 = β*(β - 2*α)/4} := by
  apply Iff.intro
  intro h'
  have : y*(2*x^2 + 2*y^2 - β) = 0 := by linear_combination h'
  simp at this
  cases this with
  | inl l => {
    rw [l] at h
    ring_nf at h
    have : x^2*(x^2 - α) = 0 :=
      by linear_combination -h
    have w : (x - α.sqrt)*(x + α.sqrt) = x^2 -α := by
    {
      ring
      rw [Real.sq_sqrt (le_of_lt ha)]
    }
    rw [← w] at this
    simp at this
    simp

    apply Or.inl
    rcases this with h1 | h2 | h3
    exact Or.inl ⟨h1, l⟩
    exact Or.inr <| Or.inl ⟨by linarith, by linarith⟩
    exact Or.inr <| Or.inr ⟨by linarith, by linarith⟩
  }
  | inr r => {
    simp
    apply Or.inr
    have crux : x^2 + y^2 = β / 2 := by linear_combination r / 2
    rw [crux] at h
    have e : (β - α)*x^2 = β^2 / 4 := by linear_combination β*crux - h
    exact ⟨by linear_combination β*crux - h, by linear_combination h - α*crux⟩
  }
  {
    simp
    intro w
    rcases w with (h1 | h2 | h3) | h4
    simp [h1]
    simp [h2]
    simp [h3]
    {
      have : (β - α) * (x^2 + y^2) = (β  - α) * (β / 2) := by linear_combination h4.left + h4.right
      have crux : β - α ≠ 0 := by {
        intro q
        have := h4.left
        simp [q] at this
        linarith [sq_pos_of_pos hb]
      }
      have : (x^2 + y^2) = β / 2 := Real.mul_left_cancel crux this
      linear_combination y*2*this
    }
  }

theorem F_right_case_nil (α β : ℝ) (ha : α > 0) (hb : β > 0)  (hba : β < 2*α) : {p : ℝ × ℝ | (β - α)*p.fst^2 = β^2 / 4 ∧ (β - α)*p.snd^2 = β*(β - 2*α)/4} = ∅ := by
  apply Set.ext
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Prod.forall]
  intros x y h
  have crux1 : β - α > 0 := kevin (sq_nonneg x) (by linarith [sq_pos_of_pos hb]) h.left
  have : (β - α)*y^2 ≥ 0 := by exact (zero_le_mul_left (by linarith)).mpr (sq_nonneg y)
  rw [mul_comm β, mul_div_assoc (β - 2 * α) β 4] at h
  have : β - 2*α ≥ 0 := kevin1 (by linarith) this h.right.symm
  linarith

#check Set.prod
theorem F_right_inter_left_zero_if (α β : ℝ) (ha : α > 0) (hb : β > 0)  (hba : 2*α < β) : {p : ℝ × ℝ | (β - α)*p.fst^2 = β^2 / 4 ∧ (β - α)*p.snd^2 = β*(β - 2*α)/4} ∩ {(0, 0), (α.sqrt, 0), (-α.sqrt, 0)} = ∅ := by
  apply Set.ext
  intro ⟨x, y⟩
  simp
  intros _ hy h
  have crux1 : y = 0 := by tauto
  simp [crux1] at hy
  have crux2 : (β - 2*α) = 0 := by {
    have : (β - 2*α) * (β / 4) = 0 := by linarith
    simp at this
    have : β ≠ 0 := ne_of_gt hb
    tauto
  }
  linarith only [crux2, hba]

theorem F_right_eq_subset_left_if (α β : ℝ) (ha : α > 0) (hb : β > 0)  (hba : β = 2*α) : {p : ℝ × ℝ | (β - α)*p.fst^2 = β^2 / 4 ∧ (β - α)*p.snd^2 = β*(β - 2*α)/4} = {(α.sqrt, 0), (-α.sqrt, 0)} := by
  apply Set.ext
  simp [hba]
  intro x y
  apply Iff.intro
  {
  ring_nf
  intro h
  have crux1 : α*(x - α.sqrt)*(x + α.sqrt) = 0 := by {
    linear_combination (norm := ring_nf) h.left
    rw [Real.sq_sqrt (by linarith only [ha])]
    ring
  }
  have crux2 : y = 0 := by {
    have : α ≠ 0 := ne_of_gt ha
    tauto
  }
  simp [crux2]
  simp [ne_of_gt ha] at crux1
  cases crux1 with
  | inl _ => exact Or.inl (by linarith)
  | inr _ => exact Or.inr (by linarith)
  }
  {
    intro h
    cases h with
    | inl h1 =>
      simp [h1, Real.sq_sqrt (by linarith only [ha])]
      ring_nf
    | inr h2 =>
      simp [h2, Real.sq_sqrt (by linarith only [ha])]
      ring_nf
  }

theorem F_right_eq (α β : ℝ) (ha : α > 0) (hb : β > 0)  (hba : β < 2*α) : {p : ℝ × ℝ | (β - α)*p.fst^2 = β^2 / 4 ∧ (β - α)*p.snd^2 = β*(β - 2*α)/4} = ({x : ℝ | (β - α)*x^2 = β^2 / 4}.prod {y : ℝ | (β - α)*y^2 = β*(β - 2*α)/4}) := by
  apply Set.ext
  intro ⟨x, y⟩
  simp only [Set.prod, Set.mem_setOf_eq]
