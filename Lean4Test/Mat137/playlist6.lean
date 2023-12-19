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

theorem help (p : ℝ → ℝ → Prop) (h1 : ∀ a : ℝ, ∃ b : ℝ, p b a) : ∃ f : ℝ → ℝ, ∀ a, p (f a) a := by
  exact Classical.skolem.mp h1
example (f g : ℝ → ℝ) (a L δ : ℝ) (hd : δ > 0) (hf : DifferentiableOn ℝ f (Set.Ico a (a + δ))) (hg : DifferentiableOn ℝ g (Set.Ico a (a + δ))) :
 (∀ x ∈ Set.Ioo a (a + δ), g x ≠ 0) →  (∀ x ∈ Set.Ioo a (a + δ), deriv g x ≠ 0) → limitR f a 0 → limitR g a 0 → (limitR (deriv f / deriv g ) a L) → (limitR (fun x => (f x - f a)/ (g x - g a)) a L) := by
{
  intros hg' hg''
  intros hfi hgi
  intro H
  have crux' := crux a (a + δ) L (by linarith) (deriv f / deriv g)
  have : ∃ c : ℝ → ℝ, ∀ x : ℝ, x ∈ Set.Ioo a (a + δ) → (a < c x ∧ c x < x) ∧ deriv f (c x) = (f x - f a) / (x - a) := by {
    apply help (fun u x => x ∈ Set.Ioo a (a + δ) → (a < u ∧ u < x) ∧ deriv f u = (f x - f a) / (x - a))

    intro x

    cases em (x ∈ Set.Ioo a (a + δ)) with
    | inl hx => {
      have w1 : a < x := by {
        simp at hx
        linarith
      }
      have : Set.Icc a x ⊆ Set.Ico a (a + δ) := by {
          simp [Set.Icc, Set.Ico]
          intros y hy1 hy2
          apply And.intro
          exact hy1

          simp at hx
          linarith [hx]
        }
      have := exists_deriv_eq_slope f w1 (ContinuousOn.mono (DifferentiableOn.continuousOn hf) this) (by {
        have w := DifferentiableOn.mono hf this
        have : Set.Ioo a x ⊆ Set.Icc a x := by exact Set.Ioo_subset_Icc_self
        exact DifferentiableOn.mono w this
      })
      match this with
      | ⟨c, hc, Hc⟩ => {
        use c
        intro _
        apply And.intro
        exact hc
        exact Hc
      }
    }
    | inr hx => {
      use 0
      intro hx'
      tauto
    }
  }
  match this with
  | ⟨c, hc⟩ => {
    specialize crux' c (by {
      intro x hx
      specialize hc x hx
      exact hc.left
    }) H
    have : limitR (fun x => ((f x - f a) / (x - a)) / (deriv g (c x))) a L := by
    {
      intros ε he
      specialize crux' ε he
      match crux' with
      | ⟨δ1, hd', Hd⟩ => {
        use min δ δ1
        use (by {
          apply lt_min_iff.mpr
          apply And.intro
          linarith
          linarith
        })
        intro x ⟨hx1, hx2⟩
        simp
        specialize hc x (by {
          simp
          apply And.intro
          linarith
          linarith [min_le_left δ δ1]
        })
        rw [← hc.right]
        apply Hd

        apply And.intro
        exact hx1
        linarith [min_le_right δ δ1]
      }
    }

  }

}

#check exists_ratio_hasDerivAt_eq_ratio_slope'
#check DifferentiableOn.continuousOn
