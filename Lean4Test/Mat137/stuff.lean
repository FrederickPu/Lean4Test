import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.KreinMilman

#check Real.continuous_mul

#check IsCompact.has_extreme_point
#check IsCompact
#check openSegment

#check Set.extremePoints
#check Set.Nonempty
#check Semiring

#check IsCompact.isBounded -- probably most useful for EVT
#check ContinuousOn.image_Icc -- most useful for IVT (could also help for EVT)

#check exists_deriv_eq_zero-- rolles theorem
#check exists_fun_eq_zero
-- #check Set.Maximum
example (S : Set ℝ) : (S.extremePoints NNReal).Nonempty → (∃ M ∈ S, ∀ x ∈ S, x ≤ M) := by
{
  intro ⟨x, hx, h⟩
  simp only [openSegment] at h
}
theorem Icc_extremeP (a b : ℝ) (hab : a < b) : ((Set.Icc a b).extremePoints ℝ).Nonempty := by
{
  apply IsCompact.has_extreme_point
  exact isCompact_Icc
  simp only [ge_iff_le, Set.nonempty_Icc]; linarith
}

#check openSegment
example (a b : ℝ) (hab : a < b) : ∃ M ∈ (Set.Icc a b), ∀ x ∈ (Set.Icc a b), x ≤ M := by
{
  have := Icc_extremeP a b hab
  simp [Set.extremePoints, Set.Nonempty] at this
  match this with
  | ⟨x, hx, h⟩ => {
    use x
    use hx
    intros y hy
    simp at hy
    specialize h hy.left hy.right
  }
}

#check Continuous
theorem EVT (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : Continuous f) :
--   ∃ c ∈ (Set.Icc a b), ∀ x ∈ (Set.Icc a b), f x ≤ f c := by
-- {
--   suffices : ((f '' (Set.Icc a b)).extremePoints ℝ).Nonempty

-- }
