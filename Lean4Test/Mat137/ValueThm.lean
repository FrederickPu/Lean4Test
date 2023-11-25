import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.KreinMilman

example (a b : ℝ) : a ≤ b →  a ≠ b → a < b := by exact fun a_1 a_2 => Ne.lt_of_le a_2 a_1
#check ContinuousOn.image_Icc -- most useful for IVT (could also help for EVT)
theorem IVT_inc' (a b M : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) (hM : f a ≤ M ∧ M ≤ f b) :
 ∃ c ∈ Set.Icc a b, f c = M := by
  have crux := ContinuousOn.image_Icc (hab) hf
  have h1 : sInf (f '' Set.Icc a b) ≤ f a := by {
    have : a ∈ Set.Icc a b := by simp; exact hab
    exact ContinuousOn.sInf_image_Icc_le hf this
  }
  have h2 : f b ≤ sSup (f '' Set.Icc a b) := by {
    have : b ∈ Set.Icc a b := by simp; exact hab
    exact ContinuousOn.le_sSup_image_Icc hf this
  }
  have : Set.Icc (f a) (f b) ⊆ Set.Icc (sInf (f '' Set.Icc a b)) (sSup (f '' Set.Icc a b)) :=
    Set.Icc_subset_Icc h1 h2
  specialize this ⟨hM.left, hM.right⟩
  rw [← crux] at this
  match this with
  | ⟨c, hc, H⟩ => use c
theorem IVT_inc (a b M : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) (hM : f a < M ∧ M < f b) :
  ∃ c ∈ Set.Ioo a b, f c = M := by
  have crux := ContinuousOn.image_Icc (le_of_lt hab) hf
  have h1 : sInf (f '' Set.Icc a b) ≤ f a := by {
    have : a ∈ Set.Icc a b := by simp; exact le_of_lt hab
    exact ContinuousOn.sInf_image_Icc_le hf this
  }
  have h2 : f b ≤ sSup (f '' Set.Icc a b) := by {
    have : b ∈ Set.Icc a b := by simp; exact le_of_lt hab
    exact ContinuousOn.le_sSup_image_Icc hf this
  }
  have : Set.Icc (f a) (f b) ⊆ Set.Icc (sInf (f '' Set.Icc a b)) (sSup (f '' Set.Icc a b)) :=
    Set.Icc_subset_Icc h1 h2
  specialize this ⟨le_of_lt hM.left, le_of_lt hM.right⟩
  rw [← crux] at this
  match this with
  | ⟨c, hc, H⟩ => {
    have ha : a ≠ c := by {
      intro h
      rw [h] at hM
      rw [H] at hM
      simp at hM
    }
    have hb : c ≠ b := by {
      intro h
      rw [← h] at hM
      rw [H] at hM
      simp at hM
    }
    use c
    apply And.intro
    exact ⟨Ne.lt_of_le ha hc.left, Ne.lt_of_le hb hc.right⟩
    exact H
  }
#check Real.ContinuousOn_neg
#check Continuous.neg
#check ContinuousOn.neg
theorem IVT_dec (a b M : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) (hM : f a > M ∧ M > f b) :
   ∃ c ∈ Set.Ioo a b, f c = M := by
   have : ContinuousOn (-f) (Set.Icc a b) := ContinuousOn.neg hf
   have := IVT_inc a b (-M) hab (-f) this (by simp; exact hM)
   match this with
   | ⟨c, hc, H⟩ => {
    use c
    use hc
    simp at H
    exact H
   }

#check ContinuousOn.image_Icc
example (a b : ℝ) (hab : a ≤ b) : a ∈ Set.Icc a b := by exact Set.left_mem_Icc.mpr hab
theorem EVT_max (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
  ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f c := by
  have crux := ContinuousOn.image_Icc (le_of_lt hab) hf
  have : sSup (f '' Set.Icc a b) ∈ Set.Icc (sInf (f '' Set.Icc a b)) (sSup (f '' Set.Icc a b)):= by {
    have : (a + b) / 2 ∈ Set.Icc a b := by simp; exact ⟨by linarith, by linarith⟩
    have crux1 := ContinuousOn.le_sSup_image_Icc hf this
    have crux2 := ContinuousOn.sInf_image_Icc_le hf this
    apply Set.right_mem_Icc.mpr
    linarith
  }
  rw [← crux] at this
  match this with
  | ⟨x, hx, H⟩ => {
    use x
    use hx
    intros y hy
    rw [H]
    exact ContinuousOn.le_sSup_image_Icc hf hy
  }
theorem EVT_min (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
  ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f c ≤ f x := by
  have crux := EVT_max a b hab (-f) (ContinuousOn.neg hf)
  match crux with
  | ⟨c, hc, H⟩ => {
    use c
    use hc
    simp at H
    simp
    exact H
  }
#check Real.image_Icc
def increasing_on (a b : ℝ) (f : ℝ → ℝ) := ∀ x₁ ∈ Set.Icc a b, ∀ x₂ ∈ Set.Icc a b, x₁ < x₂ → f x₁ < f x₂
def decreasing_on (a b : ℝ) (f : ℝ → ℝ) := ∀ x₁ ∈ Set.Icc a b, ∀ x₂ ∈ Set.Icc a b, x₁ < x₂ → f x₁ > f x₂

#check Set.InjOn
example (a b c : ℝ) : c ≤ b → Set.Icc a c ⊆ Set.Icc a b := by exact fun a_1 =>
  Set.Icc_subset_Icc_right a_1
theorem Inj_inc (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (Hab : f a < f b) (hf : ContinuousOn f (Set.Icc a b)) :
 Set.InjOn f (Set.Icc a b) → increasing_on a b f := by
{
  intro H
  apply by_contradiction
  intro h
  match EVT_max a b hab f hf with
  | ⟨c, hc, Hc⟩ => {
    have ha := Hc a (Set.left_mem_Icc.mpr (le_of_lt hab))
    have hb := Hc b (Set.right_mem_Icc.mpr (le_of_lt hab))
    have : a ≠ c := by {
      intro p
      rw [← p] at hb
      linarith
    }
    have crux1 : a < c := Ne.lt_of_le this hc.left
    cases LE.le.lt_or_eq hc.right with
    | inl l => {
      -- f a ≤ f c ≥ f b (a < c ≤ b)
      have := IVT_inc' a c (f b) (le_of_lt crux1) f (by {
        have : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hc.right
        exact ContinuousOn.mono hf this
      }) ⟨le_of_lt Hab, hb⟩
      match this with
      | ⟨d, hd, Hd⟩ => {
        have w1 : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hc.right

        specialize H (w1 hd) (Set.right_mem_Icc.mpr (le_of_lt hab)) Hd
        linarith [hd.right]
      }
    }
    | inr r => {
      rw [r] at Hc
      have crux2 := h
      simp only [increasing_on, Set.mem_Icc, not_forall] at crux2
      match crux2 with
      | ⟨x, hx, y, hy, hxy, Hxy⟩ => {
        simp at Hxy
        -- f x ≥ f y ≤ f b (x < y ≤ b)
        have : Set.Icc y b ⊆ Set.Icc a b := Set.Icc_subset_Icc_left hy.left
        have := IVT_inc' y b (f x) hy.right f (ContinuousOn.mono hf this) ⟨Hxy, Hc x hx⟩
        match this with
        | ⟨e, he, He⟩ => {
          specialize H (Set.Icc_subset_Icc_left (by linarith) he) hx He
          linarith [he.left]
        }
      }
    }
  }
}
theorem Inj_dec (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (Hab : f a > f b) (hf : ContinuousOn f (Set.Icc a b)) :
 Set.InjOn f (Set.Icc a b) → decreasing_on a b f := by
 intro H
 have := Inj_inc a b hab (-f) (by simp; exact Hab) (ContinuousOn.neg hf) (by simp [Set.InjOn] at *; exact H)
 simp [increasing_on] at this
 simp [decreasing_on]
 exact this

example (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
  deriv f a < 0 → deriv f b > 0 → ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by
  cases eq_or_ne (f a) (f b) with
  | inl l => exact fun _ _ => exists_deriv_eq_zero hab hf l
  | inr r => {
    cases Ne.lt_or_lt r with
    | inl l => {
      intros ha hb

    }
  }
#check exists_deriv_eq_zero-- rolles theorem
#check exists_deriv_eq_slope
#check intermediate_value_Icc
#check Set.hasMax
