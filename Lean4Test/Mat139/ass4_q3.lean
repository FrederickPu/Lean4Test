import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable


#check ContinuousOn

#check MeasureTheory.set_integral_nonneg


-- first show that ∫ g t - f t ≥ 0
-- then show ∫ g t - ∫ f t ≥ 0

theorem integral_le (a b : ℝ) (hab : a ≤ b) (f g : ℝ → ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b)  (hg : IntervalIntegrable g MeasureTheory.volume a b): (∀ x ∈ Set.Icc a b, f x ≤ g x) → ∫ x in a..b, f x ≤ ∫ x in a..b, g x := by {
  intro h
  have : ∀ x ∈ Set.Icc a b, g x - f x ≥ 0 := by {
    intro x hx
    specialize h x hx
    linarith
  }

  have : 0 ≤ ∫ x in a..b, g x - f x := intervalIntegral.integral_nonneg hab this
  have : ∫ (x : ℝ) in a..b, g x - f x = (∫ (x : ℝ) in a..b, g x )- ∫ (x : ℝ) in a..b, f x := by {
   have := intervalIntegral.integral_sub hg hf
   simp at this
   exact this
  }
  linarith
}

theorem integral_subset_right (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (f : ℝ → ℝ) (hf1 : IntervalIntegrable f MeasureTheory.volume a b) (hf2 : IntervalIntegrable f MeasureTheory.volume b c) : (∀ x ∈ Set.Icc a c, f x ≥ 0) → ∫ x in a..b, f x ≤ ∫ x in a..c, f x := by {
  intro hsub
  have : ∫ (x : ℝ) in a..c, f x = (∫ (x : ℝ) in a..b, f x)  + ∫ (x : ℝ) in b..c, f x := by {
    apply Eq.symm
    exact intervalIntegral.integral_add_adjacent_intervals hf1 hf2
  }
  have : ∫ (x : ℝ) in b..c, f x ≥ 0 := by {
    have : ∀ x ∈ Set.Icc b c, 0 ≤ f x := by {
      intro x hx
      have : x ∈ Set.Icc a c := by {
        apply And.intro
        linarith [hx.left]
        exact hx.right
      }
      exact hsub _ this
    }
    exact intervalIntegral.integral_nonneg hbc this
  }
  linarith
}
-- ∫a^b = ∫0^b - ∫0^a
-- F a a - sup = - F a c
variables (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.uIcc a b)) (F : ℝ → ℝ → ℝ) (hF : ∀ c ∈ Set.Icc a b, F c = fun x => ∫ t in c..x, f t)

example : ∃ G : ℝ → ℝ, ∀ c ∈ Set.Icc a b, G ≠ F c := by
{
  use (fun x => F a x - (sSup {F a c | c ∈ Set.Icc a b} + 1))
  intro c hc
  intro h
  have := congrFun h a
  simp at this
  rw [hF] at this
  simp only [intervalIntegral.integral_same, zero_sub] at this
  rw [hF] at this
  simp only at this
  have w : ∫ (t:ℝ) in c..a, f t = -∫ t in a..c, f t := intervalIntegral.integral_symm a c
  rw [w] at this
  apply False.elim
  have : (sSup {x | ∃ c, (a ≤ c ∧ c ≤ b) ∧ ∫ (t : ℝ) in a..c, f t = x} + 1) = ∫ (t : ℝ) in a..c, f t := by linarith
  have : ∫ (t : ℝ) in a..c, f t ∈ {x | ∃ c, (a ≤ c ∧ c ≤ b) ∧ ∫ (t : ℝ) in a..c, f t = x} := by {
    simp
    use c
    use hc
  }
  have : ∫ (t : ℝ) in a..c, f t ≤ sSup {x | ∃ c, (a ≤ c ∧ c ≤ b) ∧ ∫ (t : ℝ) in a..c, f t = x} := by {
    rw [Real.le_sSup_iff]
    intro ε he
    use ∫ (t : ℝ) in a..c, f t
    simp
    apply And.intro
    use c
    use hc
    exact he

    use ∫ t in a..b, |f t|
    rw [mem_upperBounds]

    intro y hy
    simp at hy
    match hy with
    | ⟨c, hc, H⟩ => {
      rw [← H]
      have :  ∫ (t : ℝ) in a..c, f t ≤ (∫ (t : ℝ) in a..c, |f t|) := by {
        apply integral_le
        exact hc.left
        have := hc.left
        have : Set.uIcc a c = Set.Icc a c := by exact Set.uIcc_of_le hc.left
        have : Set.uIcc a b = Set.Icc a b := by exact Set.uIcc_of_le hab
        have : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hc.right
        have : ContinuousOn f (Set.uIcc a c) := by {
          rw [Set.uIcc_of_le hc.left]
          rw [Set.uIcc_of_le hab] at hf
          exact ContinuousOn.mono hf this
        }
        exact ContinuousOn.intervalIntegrable this

        have : ContinuousOn (fun x => |f x|) (Set.uIcc a c) := by {
          have := ContinuousOn.abs hf
          rw [Set.uIcc_of_le hab] at this
          rw [Set.uIcc_of_le hc.left]
          exact ContinuousOn.mono this (Set.Icc_subset_Icc_right hc.right)
        }
        exact ContinuousOn.intervalIntegrable this

        intro x hx
        exact le_abs_self (f x)
      }
      have := hc.right
      have : ∀ x, |f x| ≥ 0 := by {
        intro x
        exact abs_nonneg (f x)
      }
      have : ∫ (t : ℝ) in a..c, |f t| ≤ ∫ (t : ℝ) in a..b, |f t| := by {
        apply integral_subset_right
        exact hc.left
        exact hc.right
        have : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hc.right
        have : ContinuousOn f (Set.uIcc a c) := by {
          rw [Set.uIcc_of_le hc.left]
          rw [Set.uIcc_of_le hab] at hf
          exact ContinuousOn.mono hf this
        }
        have : ContinuousOn (fun x => |f x|) (Set.uIcc a c) := by exact ContinuousOn.abs this
        exact ContinuousOn.intervalIntegrable this
        have : ContinuousOn (fun x => |f x|) (Set.uIcc c b) := by {
          have : Set.Icc c b ⊆ Set.Icc a b :=  Set.Icc_subset_Icc_left hc.left
          have : ContinuousOn f (Set.uIcc c b) := by {
            rw [Set.uIcc_of_le hc.right]
            rw [Set.uIcc_of_le hab] at hf
            exact ContinuousOn.mono hf this
          }
          exact ContinuousOn.abs this
        }
        exact ContinuousOn.intervalIntegrable this
        intro x hx
        exact this x
      }
      linarith
    }
    use ∫ (t : ℝ) in a..a, f t
    simp
    use a
    simp
    exact hab
  }
  linarith
  exact hc
  simp
  exact hab
}

#check ContinuousOn.intervalIntegrable
