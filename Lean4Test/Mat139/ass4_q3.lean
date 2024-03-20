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

-- question 3 a
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

theorem atTop_nhds (a : ℝ) (f : ℝ → ℝ) : Filter.Tendsto f (Filter.atTop) (nhds a) ↔ ∀ ε > 0, ∃ N, ∀ x : ℝ, x ≥ N → |f x - a| < ε := by {
  rw [Filter.tendsto_def]
  apply Iff.intro
  intro h ε he
  have : Metric.ball a ε ∈ nhds a := Metric.ball_mem_nhds a he
  specialize h _ this
  simp only [Filter.mem_atTop_sets, Set.mem_preimage, Metric.mem_ball] at h
  exact h

  intro h
  intro s hs
  rw [mem_nhds_iff] at hs
  match hs with
  | ⟨t, ht, ⟨H, ha⟩⟩ => {
    rw [Metric.isOpen_iff] at H
    specialize H a ha
    simp only [Filter.mem_atTop_sets, Set.mem_preimage]
    match H with
    | ⟨ε, he, H⟩ => {
      specialize h ε he
      match h with
      | ⟨N, h⟩ => {
        use N
        intro x hx
        specialize h x hx
        specialize ht <| H h
        exact ht
      }
    }
  }
}

example (x : ℝ) : (∀ ε > 0, x < ε) → x ≤ 0 := by exact fun a => le_of_forall_lt' a
def increasing (f : ℝ → ℝ) := ∀ x y : ℝ, x < y → f x < f y
example (f : ℝ → ℝ) (hf : increasing f) (L : ℝ): Filter.Tendsto f Filter.atTop (nhds L) →
  ∀ᶠ x in Filter.atTop, f x < L := by {
  intro h
  have : sSup (f '' Set.univ) = L := by {
    have : sSup (f '' Set.univ) - L = 0 := by
      suffices : ∀ ε > 0, sSup (f '' Set.univ) - L < ε
      have := le_of_forall_lt' this
      have : L ≤ sSup (f '' Set.univ) := by sorry
      linarith

      sorry
    linarith
  }
  rw [← this]
  simp
  rw [atTop_nhds] at h
  specialize h 1 (by linarith)
  match h with
  | ⟨N, H⟩ => {
    use N
    intro b hb
    have := H (b + 1) (by linarith)
    have : f (b + 1) ≤ sSup (f '' Set.univ) := by {  b bbnn,m,m
      rw [Real.le_sSup_iff]
      intro ε he
      use (f (b + 2))
      simp
      have := hf (b + 1) (b + 2) (by linarith)
      linarith..
    }
  }
}
