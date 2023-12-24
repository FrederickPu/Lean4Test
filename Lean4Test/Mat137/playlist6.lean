import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.bounds
import Mathlib.Tactic

def limitR (f : ℝ → ℝ) (a L : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < x - a ∧ x - a < δ → |f x - L| < ε

theorem crux (a b L : ℝ) (hab : a < b) (H : ℝ → ℝ) (c : ℝ → ℝ) (hc : ∀ x : ℝ, x ∈ Set.Ioo a b → a < c x ∧ c x < x) :
  limitR H a L → limitR (H ∘ c) a L := by
  intro hH
  intros ε he
  specialize hH ε he
  match hH with
  | ⟨δ, hd, Hd⟩ => {
    use min δ (b - a)
    use (by {
      apply lt_min_iff.mpr
      apply And.intro
      linarith
      linarith
    })
    intro x ⟨hxL, hxR⟩
    specialize hc x (by {
      simp
      exact ⟨by linarith [hxL], by {
        have :  min δ (b - a) ≤ b - a := min_le_right δ (b - a)
        linarith
      }⟩
    })
    specialize Hd (c x) ⟨by linarith [hc], by {
      linarith [min_le_left δ (b - a)]
    }⟩
    exact Hd
  }

#check deriv_const_mul
#check DifferentiableWithinAt
#check DifferentiableOn.differentiableAt
#check iInf
#check Filter.GenerateSets
#check Set.mem_iUnion
#check Set.mem_inf

-- cool Filter proof
example (a b : ℝ) (hc : c ∈ Set.Ioo a b) : Set.Ioo a b ∈ nhds c := by {
  rw [nhds]
  have : IsOpen <| Set.Ioo a b := by exact isOpen_Ioo
  rw [Filter.iInf_eq_generate]

  apply Filter.mem_generate_of_mem
  rw [Set.mem_iUnion]
  use Set.Ioo a b
  -- simp
  -- simp only [Filter.principal_univ, Filter.mem_sets]
  simp only [Set.mem_setOf_eq, hc, this]
  simp only [iInf_pos, Filter.mem_top]
  simp only [Filter.mem_sets, Filter.mem_principal]
  exact Eq.subset rfl
}

theorem help (p : ℝ → ℝ → Prop) (h1 : ∀ a : ℝ, ∃ b : ℝ, p b a) : ∃ f : ℝ → ℝ, ∀ a, p (f a) a := by
  exact Classical.skolem.mp h1
theorem cauchy_mvt (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b)) (hfd : DifferentiableOn ℝ f (Set.Ioo a b)) (hgc : ContinuousOn g (Set.Icc a b)) (hgd : DifferentiableOn ℝ g (Set.Ioo a b)) (hg1 : ∀ x ∈ Set.Ioo a b, deriv g x ≠ 0) (hg2 : g b - g a ≠ 0): ∃ c ∈ Set.Ioo a b, deriv f c / deriv g c = (f b - f a) / (g b - g a) := by
  let F := fun x => (g b - g a) * f x - (f b - f a) * g x - (g b * f a - f b * g a)
  have w1 : F a = 0 := by {
    simp [F]
    ring
  }
  have w2 : F b = 0 := by {
    simp [F]
    ring
  }
  have : ∃ c ∈ Set.Ioo a b, deriv F c = 0 := exists_deriv_eq_zero hab (by {
    apply ContinuousOn.sub
    apply ContinuousOn.sub
    exact ContinuousOn.mul continuousOn_const hfc
    exact ContinuousOn.mul continuousOn_const hgc
    exact continuousOn_const
  }) (by linarith)
  match this with
  | ⟨c, hc, Hc⟩ => {
    simp [F] at Hc

    have : Set.Ioo a b ∈ nhds c := by {
      exact IsOpen.mem_nhds isOpen_Ioo hc
    }
    have hfc' : DifferentiableAt ℝ (fun x => f x) c := DifferentiableOn.differentiableAt hfd (IsOpen.mem_nhds isOpen_Ioo hc)
    have hgc' : DifferentiableAt ℝ (fun x => g x) c := DifferentiableOn.differentiableAt hgd (IsOpen.mem_nhds isOpen_Ioo hc)
    have h1 : DifferentiableAt ℝ (fun x => (g b - g a) * f x) c := DifferentiableAt.const_mul hfc' (g b - g a)
    have h2 : DifferentiableAt ℝ (fun x => (f b - f a) * g x) c := DifferentiableAt.const_mul hgc' (f b - f a)

    rw [deriv_sub (DifferentiableAt.sub h1 h2) (differentiableAt_const _), deriv_const, deriv_sub h1 h2] at Hc
    rw [deriv_const_mul _ hfc'] at Hc
    rw [deriv_const_mul _ hgc'] at Hc
    rw [sub_zero] at Hc
    use c
    use hc
    field_simp [hg1 c hc]
    linarith
  }

-- specialize case of l'hopital's rule
example (f g : ℝ → ℝ) (a L δ : ℝ) (hd : δ > 0) (hfc : ContinuousOn f (Set.Icc a (a + δ))) (hfd : DifferentiableOn ℝ f (Set.Ico a (a + δ))) (hgc : ContinuousOn g (Set.Icc a (a + δ))) (hgd : DifferentiableOn ℝ g (Set.Ico a (a + δ))) :
 (∀ x ∈ Set.Ioo a (a + δ), g x ≠ 0) →  (∀ x ∈ Set.Ioo a (a + δ), deriv g x ≠ 0) → (∀ x ∈ Set.Ioo a (a + δ), g x - g a ≠ 0) → limitR f a 0 → limitR g a 0 → (limitR (deriv f / deriv g ) a L) → (limitR (fun x => (f x - f a)/ (g x - g a)) a L) := by
{
  intros hg' hg'' hg'''
  intros hfi hgi
  intro H
  have crux' := crux a (a + δ) L (by linarith) (deriv f / deriv g)
  have : ∃ c : ℝ → ℝ, ∀ x ∈ Set.Ioo a (a + δ), (a < c x ∧ c x < x) ∧ deriv f (c x) / deriv g (c x) = (f x - f a) / (g x - g a) := by
  {
    apply help (fun u x => x ∈ Set.Ioo a (a + δ) → (a < u ∧ u < x) ∧ deriv f u / deriv g u = (f x - f a) / (g x - g a))
    intro x
    cases em (x ∈ Set.Ioo a (a + δ)) with
    | inl l => {
      have := cauchy_mvt f g a x l.left (by {
        have : Set.Icc a x ⊆ Set.Icc a (a + δ) := Set.Icc_subset_Icc_right (le_of_lt l.right)
        exact ContinuousOn.mono hfc this
      }) (by {
        have : Set.Ico a x ⊆ Set.Ico a (a + δ) := Set.Ico_subset_Ico_right (le_of_lt l.right)
        exact DifferentiableOn.mono hfd (Set.Subset.trans (Set.Ioo_subset_Ico_self) this)
      }) (by {
        have : Set.Icc a x ⊆ Set.Icc a (a + δ) := Set.Icc_subset_Icc_right (le_of_lt l.right)
        exact ContinuousOn.mono hgc this
      }) (by {
        have : Set.Ico a x ⊆ Set.Ico a (a + δ) := Set.Ico_subset_Ico_right (le_of_lt l.right)
        exact DifferentiableOn.mono hgd (Set.Subset.trans (Set.Ioo_subset_Ico_self) this)
      }) (by {
        intro y hy
        have := le_of_lt l.right
        have : Set.Ioo a x ⊆ Set.Ioo a (a + δ) := Set.Ioo_subset_Ioo_right this
        exact hg'' y (this hy)
      }) (hg''' x l)
      match this with
      | ⟨c, hc, Hc⟩ => {
        use c
        intro hx
        apply And.intro
        exact hc
        exact Hc
      }
    }
    | inr r => {
      use 0
      intro hx
      exact (r hx).elim
    }
  }
  match this with
  | ⟨c, Hc⟩ => {
    specialize crux' c (by {
      intro x hx
      specialize Hc x hx
      exact Hc.left
    }) H

    intro ε he
    specialize crux' ε he
    match crux' with
    | ⟨δ', hd, Hd⟩ => {
      use min δ δ'
      use (by {
        apply lt_min_iff.mpr
        apply And.intro
        linarith
        linarith
      })
      intro x hx
      specialize Hd x ⟨hx.left, by linarith [hx, min_le_right δ δ']⟩
      simp only [Function.comp_apply, Pi.div_apply] at Hd
      specialize Hc x ⟨by linarith, by linarith [hx, min_le_left δ δ']⟩
      rw [Hc.right] at Hd
      exact Hd
    }
  }
}

#check exists_ratio_hasDerivAt_eq_ratio_slope'
#check DifferentiableOn.continuousOn
