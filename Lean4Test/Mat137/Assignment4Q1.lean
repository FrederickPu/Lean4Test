import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (α β x y y' : ℝ) (h : 2*(x^2+y^2)*(2*x + 2*y*y') = (α*2*x + β*2*y*y')) :
  (2*x^2*y+2*y^3 - β*y)*y' = -(2*x^3+2*x*y^2 - α*x) := by
  linear_combination h/2
def F (α β x y : ℝ) : ℝ := (2*x^2*y+2*y^3 - β*y)
def G (α β x y : ℝ) : ℝ := (2*x^3+2*x*y^2 - α*x)

theorem F_G_symm (α β x y : ℝ) : F α β x y = G β α y x := by
  rw [F, G]
  ring

def all_sign_2 (a b : ℝ) : Set (ℝ × ℝ) := {(a,-b), (a, b), (-a, b),(-a, -b)}
theorem all_sign_sq (a b : ℝ) : all_sign_2 a b = {p : ℝ × ℝ | p.fst^2 = a^2 ∧ p.snd^2 = b^2} := by
  apply Set.ext
  intros p
  apply Iff.intro

  exact fun h => by
    simp only [all_sign_2, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h1 | h2 | h3 | h4
    simp [h1]
    simp [h2]
    simp [h3]
    simp [h4]

  exact fun h => by
    simp [all_sign_2]
    have h1 : (p.fst - a)*(p.fst + a) = 0 := by linear_combination h.left
    simp at h1
    have h2 : (p.snd - b)*(p.snd + b) = 0 := by linear_combination h.right
    simp at h2

    have w : p = (p.1, p.2)  := by rfl
    rcases h1, h2 with ⟨ha | ha, hb | hb⟩;
    repeat' (
      rw [w]
      simp only [Prod.mk.inj_iff]
      repeat (
        first | apply Or.inl; exact ⟨by linarith, by linarith⟩ | apply Or.inr | exact ⟨by linarith, by linarith⟩
      )
    )

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

theorem Real.mul_left_cancel {a b c: ℝ} : c ≠ 0 →  c*a = c*b → a= b := by
  intros hc h
  have : c⁻¹ * (c*a) = c⁻¹*(c*b) := by exact congrArg (HMul.hMul c⁻¹) h
  simp only [← mul_assoc, inv_mul_cancel hc, one_mul] at this
  exact this

theorem F_zero_iff (α β x y : ℝ) (ha : α > 0) (hb : β > 0) (h : α*x^2 + β*y^2 = (x^2 + y^2)^2) : F α β x y = 0 ↔ (x, y) ∈ ({(0, 0), (α.sqrt, 0), (-α.sqrt, 0)} : Set (ℝ × ℝ)) ∪ {p : ℝ × ℝ | (β - α)*p.fst^2 = β^2 / 4 ∧ (β - α)*p.snd^2 = β*(β - 2*α)/4} := by
  rw [F]
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

theorem F_sol_lt (α β x y : ℝ) (ha : α > 0) (hb : β > 0)  (hba : 2*α < β) (h : α*x^2 + β*y^2 = (x^2 + y^2)^2)  : F α β x y = 0  ↔ (x, y) ∈ ({(0, 0), (α.sqrt, 0), (-α.sqrt, 0)} : Set (ℝ × ℝ)) ∪ all_sign_2 (β/ (2*(β - α).sqrt)) ((β*(β - 2*α)).sqrt/(2*(β - α).sqrt)) := by
  have hb2a : β * (β - 2*α) ≥ 0 := by
  {
    have : (β - 2*α) ≥ 0 := by linarith
    exact (zero_le_mul_left hb).mpr this
  }
  have hba1 : β - α ≥ 0 := by linarith
  have hba2 : β - α ≠ 0 := by linarith

  rw [F_zero_iff α β x y ha hb h]
  simp only [Set.mem_union]
  apply or_congr_right
  apply Iff.intro
  intro hw
  rw [all_sign_sq]
  simp

  simp at hw

  -- get rid of square roots in denominator
  ring_nf
  simp [Real.sq_sqrt hba1]; rw [Real.sq_sqrt]

  apply And.intro
  linear_combination (norm := ring_nf) hw.left / (β - α)
  {
    have : β - α ≠ 0 := by linarith
    field_simp
    ring
  }
  linear_combination (norm := ring_nf) hw.right / (β - α)
  {
    have : β - α ≠ 0 := by linarith
    field_simp
    ring
  }
  linarith only [hb2a]

  rw [all_sign_sq]
  simp
  intros h1 h2

  -- get rid of square roots in denominator
  ring_nf at h2
  simp [Real.sq_sqrt hba1] at h2; rw [Real.sq_sqrt] at h2

  apply And.intro
  linear_combination (norm := ring_nf) (β - α)*h1
  {
    field_simp
    ring
  }
  linear_combination (norm := ring_nf) (β - α)*h2
  {
    field_simp
    ring
  }
  linarith only [hb2a]

theorem F_sol_ge (α β x y : ℝ) (ha : α > 0) (hb : β > 0)  (hba : β ≤ 2*α) (h : α*x^2 + β*y^2 = (x^2 + y^2)^2)  : F α β x y = 0 ↔ (x, y) ∈ ({(0, 0), (α.sqrt, 0), (-α.sqrt, 0)} : Set (ℝ × ℝ)) := by
  rw [F_zero_iff α β x y ha hb h, Set.mem_union]
  cases lt_or_eq_of_le hba with
  | inl hba =>
  rw [F_right_case_nil α β ha hb hba]
  simp only [Set.mem_empty_iff_false, or_false]
  | inr hba =>
  have := F_right_eq_subset_left_if α β ha hb hba
  rw [F_right_eq_subset_left_if α β ha hb hba]
  simp

-- G stuff
example (α β x y : ℝ) (ha : α > 0) (hb : β > 0) (h : α*x^2 + β*y^2 = (x^2 + y^2)^2) : G α β x y = 0 ↔ (x, y) ∈ ({(0, 0), (0, β.sqrt), (0, -β.sqrt)} : Set (ℝ × ℝ)) ∪ {p : ℝ × ℝ | (α - β)*p.snd^2 = α^2 / 4 ∧ (α - β)*p.fst^2 = α*(α - 2*β)/4} := by
  simp [F_G_symm]
  have := F_zero_iff β α y x hb ha (by linear_combination h)
  simp at this
  tauto

example (α β x y : ℝ) (ha : α > 0) (hb : β > 0) (h : α*x^2 + β*y^2 = (x^2 + y^2)^2) (hba : 2*α < β) : F α β x y = 0 ∧ ¬ G α β x y = 0 ↔ (x, y) ∈ {(-α.sqrt, 0), (α.sqrt, 0)} ∪ all_sign_2 (β/ (2*(β - α).sqrt)) ((β*(β - 2*α)).sqrt/(2*(β - α).sqrt)) := by
  rw [F_sol_lt α β x y ha hb hba h, ← F_G_symm, F_sol_ge β α y x hb ha (by linarith only [ha, hb, hba]) (by linear_combination h)]
  rw [all_sign_sq]
  simp
  apply Iff.intro
  exact fun ⟨h1, h2⟩ => by
    cases h1 with
    | inl hl => {
      left
      simp only [Set.mem_singleton_iff, Set.mem_insert_iff, zero_eq_neg, Prod.mk.injEq] at hl
      have : ¬ (x = 0 ∧ y = 0) := by tauto
      tauto
    }
    | inr hr => {
      simp at hr
      right
      exact hr
    }
  exact fun h => by
    cases h with
    | inl hl => {
      apply And.intro
      tauto
      exact fun w => by
        have crux1 : x = 0 := by tauto
        have crux2 : α.sqrt > 0 := by exact Real.sqrt_pos.mpr ha
        cases hl with
        | inl hll => {
          rw [hll.left] at crux1
          linarith
        }
        | inr hlr => {
          rw [hlr.left] at crux1
          linarith
        }
      }
    | inr hr => {
      apply And.intro
      tauto
      exact fun w => by
        have crux1 : x = 0 := by tauto
        ring_nf at hr
        simp at hr
        rw [Real.sq_sqrt] at hr
        have := hr.left
        simp [crux1] at this
        cases this with
        | inl _ => linarith
        | inr _ => linarith

        {
          linarith
        }
      }

example (α β x y : ℝ) (ha : α > 0) (hb : β > 0) (h : α*x^2 + β*y^2 = (x^2 + y^2)^2) (hba : β ≤ 2*α) : F α β x y = 0 ∧ ¬ G α β x y = 0 ↔ (x, y) ∈ ({(-α.sqrt, 0), (α.sqrt, 0)} : Set (ℝ × ℝ)) := by
{
  rw [F_sol_ge α β x y ha hb hba h, ← F_G_symm, F_zero_iff β α y x hb ha (by linear_combination h)]
  simp only [Set.mem_union]
  apply Iff.intro
  exact fun ⟨h1, h2⟩ => by
    simp at h1
    cases h1 with
    | inl e => simp [e] at h2
    | inr f => simp at f; simp; tauto
  exact fun h => by
  {
    apply And.intro
    rcases h with h1 | h2
    rw [h1]; simp
    rw [h2]; simp

    simp at h
    intro w
    simp at w
    cases w with
    | inl hl =>
      have : Real.sqrt α = 0 ∨ 0 = Real.sqrt β := by {
        rcases hl with h1 | h2 | h3
        simp [h1] at h; tauto
        simp [h2] at h; tauto
        simp [h3] at h; tauto
      }
      have : α.sqrt ≠ 0 := by exact Real.sqrt_ne_zero'.mpr ha
      have : β.sqrt ≠ 0 := by exact Real.sqrt_ne_zero'.mpr hb
      tauto

    | inr hr => {
      have : y = 0 := by tauto
      rw [this] at hr
      simp at hr
      have : α^2 > 0 := by exact sq_pos_of_pos ha
      linarith
    }

  }
}
