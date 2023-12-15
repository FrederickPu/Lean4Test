import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Asymptotics.Asymptotics
-- import Lean4Test.Mat137.eternal_sadness

#check Asymptotics.IsLittleO

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
def increasing_on (S : Set ℝ) (f : ℝ → ℝ) := ∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ < x₂ → f x₁ < f x₂
def decreasing_on (a b : ℝ) (f : ℝ → ℝ) := ∀ x₁ ∈ Set.Icc a b, ∀ x₂ ∈ Set.Icc a b, x₁ < x₂ → f x₁ > f x₂

#check Set.InjOn
example (a b c : ℝ) : c ≤ b → Set.Icc a c ⊆ Set.Icc a b := by exact fun a_1 =>
  Set.Icc_subset_Icc_right a_1
theorem Inj_inc (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (Hab : f a < f b) (hf : ContinuousOn f (Set.Icc a b)) :
 Set.InjOn f (Set.Icc a b) → increasing_on (Set.Icc a b) f := by
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

theorem dec_or_inc_of_Inj (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
 Set.InjOn f (Set.Icc a b) → increasing_on (Set.Icc a b) f ∨ decreasing_on a b f := by
 intro H
 cases eq_or_ne (f a) (f b) with
 | inl l => {
  have := H (Set.right_mem_Icc.mpr (le_of_lt hab)) (Set.left_mem_Icc.mpr (le_of_lt hab)) l
  linarith
 }
 | inr r => {
  cases Ne.lt_or_lt r with
  | inl l => {
    left
    exact Inj_inc a b hab f l hf H
  }
  | inr r => {
    right
    exact Inj_dec a b hab f r hf H
  }
 }

#check image_sub_le_mul_sub_of_deriv_le
#check fderiv

#check Asymptotics.isLittleO_iff
#check deriv

#check hasDerivAt_iff_tendsto_slope_zero
#check Filter.Tendsto
#check mem_nhds_iff
#check UniformSpace.ball
#check UniformSpace.mem_ball_self
#check IsGLB

#check nhds
#check Filter

example (α : Type) (L R : Filter α) : ∀ x, x ∈ L ⊓ R → x ∈ L := by {
  intro x
  intro hx
  rw [Filter.mem_inf_iff] at hx
}

#check hasDeriv_of_hasFderiv
theorem tendsto_imp (a L : ℝ) (f : ℝ → ℝ) : Filter.Tendsto f (nhdsWithin a {a}ᶜ) (nhds L) → (∀ ε > 0, ∃ δ > (0:ℝ), ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε) := by
  rw [Filter.tendsto_def]
  simp only [mem_nhds_iff]
  simp only [Filter.map, nhdsWithin, Filter.mem_inf_iff]
  simp only [mem_nhds_iff]
  intro h
  intros ε he
  specialize h {x | |x - L| < ε} (by {
    use ({x | |x - L| < ε})
    apply And.intro
    exact Eq.subset rfl
    apply And.intro
    exact Metric.isOpen_ball
    simp; exact he
  })
  simp only [Metric.isOpen_iff] at h
  match h with
  | ⟨t1, ⟨t, ht, Ht⟩, t2, ht2, H⟩ =>
  {
    simp only [Set.preimage_setOf_eq] at H
    match Ht.left a Ht.right with
    | ⟨δ, hd, Hd⟩ => {
      use δ; use hd
      simp [Metric.ball, dist] at Hd
      simp at ht2
      intros x hx
      have crux1 : x ∈ t1 := ht <| Hd hx.right
      have crux2 : x ∈ t2 := ht2 <| dist_pos.mp hx.left
      have : x ∈ t1 ∩ t2 := Set.mem_inter crux1 crux2
      rw [← H] at this
      exact this
    }
  }

theorem neg_deriv_dec (f : ℝ → ℝ) (f' a : ℝ) : f' < 0 → HasDerivAt f f' a → ∃ δ > 0, ∀ x, 0 < x ∧ x < δ → f a > f (a + x) := by
{
  intros hf' hfd
  rw [hasDerivAt_iff_tendsto_slope_zero] at hfd
  apply tendsto_imp at hfd
  specialize hfd (-f') (by linarith)
  match hfd with
  | ⟨δ, hd, Hd⟩ => {
    use δ
    use hd
    intros x hx
    specialize Hd x
    simp only [sub_zero] at Hd
    rw [abs_of_pos hx.left] at Hd
    specialize Hd hx
    have : -(-f') < x⁻¹ * (f (a + x) - f a) - f' ∧ x⁻¹ * (f (a + x) - f a) - f' < -f' := abs_lt.mp Hd
    have : x⁻¹ * (f (a + x) - f a) < 0 := by linarith [this.right]
    have : x * (x⁻¹ * (f (a + x) - f a)) < x*0 := by exact (mul_lt_mul_left hx.left).mpr this
    rw [mul_zero, ← mul_assoc, mul_inv_cancel, one_mul] at this
    linarith

    linarith
  }
}

#check hasDerivAt_deriv_iff
#check Continuous.neg
#check ContinuousAt.neg
#check Continuous.comp
#check (Continuous.neg continuous_id')
#check differentiable_id
example (a : ℝ) (f : ℝ → ℝ) : Continuous (fun (x:ℝ) => x) := by exact continuous_id'

theorem crux_invar (a : ℝ) {f : ℝ → ℝ} (hf' : Differentiable ℝ f) : deriv (fun x => f (-x)) a  = - deriv f (-a) := by
{
  have : deriv (f ∘ (fun x => (-x))) a = - deriv f (-a) := by
    rw [deriv.comp, deriv.neg]
    simp
    exact hf' _
    exact Differentiable.neg differentiable_id _
  simp [Function.comp] at this
  exact this
}
example (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) (hf' : Differentiable ℝ f) :
  deriv f a < 0 → deriv f b > 0 → ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by
  wlog h' : f a ≠ f b
  simp at h'
  intros _ _
  exact exists_deriv_eq_zero hab hf h'

  wlog h : (f a < f b)
  simp at h
  have h : f b < f a := Ne.lt_of_le (id (Ne.symm h')) h
  specialize this (-b) (-a) (by linarith) (fun x => f (-x)) (by {
    have : ContinuousOn (f ∘ (fun x => -x)) (Set.Icc (-b) (-a)) := by
    {
      have w: ContinuousOn (fun x => -x) (Set.Icc (-b) (-a)) := ContinuousOn.neg continuousOn_id
      have u : Set.MapsTo (fun x => -x) (Set.Icc (-b) (-a)) (Set.Icc a b) := by {
        intro x
        simp
        exact fun hx1 hx2 => ⟨by linarith, by linarith⟩
      }
      exact ContinuousOn.comp hf w u
    }
    simp only [Function.comp] at this
    exact this
  })
  specialize this (by {
    have : Differentiable ℝ (f ∘ (fun x => -x)) :=
      Differentiable.comp hf' <| Differentiable.neg differentiable_id
    simp only [Function.comp] at this
    exact this
  })
  simp only [neg_neg] at this
  specialize this h'.symm h
  rw [crux_invar (-b) hf', crux_invar (-a) hf'] at this
  simp at this
  intros hfa hfb
  specialize this hfb hfa
  match this with
  | ⟨c, hc⟩ => {
    use -c
    apply And.intro
    exact ⟨by linarith [hc.left.right], by linarith [hc.left.left]⟩
    rw [crux_invar c hf'] at hc
    linarith
  }

  {
    wlog w : Set.InjOn f (Set.Icc a b)
    {
      simp only [not_forall, Set.InjOn] at w
      match w with
      | ⟨x, hx, y, hy, Hf, H⟩ => {
        cases Ne.lt_or_lt H with
        | inl l => {
          have crux : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset (Set.Icc a b) hx hy
          have : ContinuousOn f (Set.Icc x y) := ContinuousOn.mono hf crux
          have := exists_deriv_eq_zero l this Hf
          intros _ _
          match this with
          | ⟨c, hc, Hc⟩ => {
            use c
            simp
            simp at hc
            apply And.intro
            apply And.intro
            linarith [hc.left, hx.left]
            linarith [hc.right, hy.right]
            exact Hc
          }
        }
        | inr r => {
          have crux : Set.Icc y x ⊆ Set.Icc a b := Set.Icc_subset (Set.Icc a b) hy hx
          have : ContinuousOn f (Set.Icc y x) := ContinuousOn.mono hf crux
          have := exists_deriv_eq_zero r this Hf.symm
          intros _ _
          match this with
          | ⟨c, hc, Hc⟩ => {
            use c
            simp
            simp at hc
            apply And.intro
            apply And.intro
            linarith [hc.left, hy.left]
            linarith [hc.right, hx.right]
            exact Hc
          }
        }
      }
    }
    have crux1 := Inj_inc a b hab f h hf w
    intros ha hb
    have crux2 := neg_deriv_dec f (deriv f a) a ha (by {
        have : deriv f a ≠ 0 := by exact LT.lt.ne ha
        specialize hf' a
        exact hasDerivAt_deriv_iff.mpr hf'
      })
    match crux2 with
    | ⟨δ, hd, Hd⟩ => {
      specialize Hd (min (δ / 2) (b - a)) (by {
        apply And.intro
        {
          apply lt_min_iff.mpr
          apply And.intro
          linarith
          linarith
        }
        apply min_lt_iff.mpr
        left
        linarith
      })
      have : a < min (a + δ / 2) b := by {
        apply lt_min_iff.mpr
        apply And.intro
        linarith
        exact hab
      }
      apply crux1 at this
      simp only [add_sub_cancel'_right ,← min_add_add_left a (δ / 2) (b - a)] at Hd
      linarith
      exact Set.left_mem_Icc.mpr (le_of_lt hab)
      simp
      exact ⟨by linarith, by linarith⟩
    }

  }
  -- cases eq_or_ne (f a) (f b) with
  -- | inl l => exact fun _ _ => exists_deriv_eq_zero hab hf l
  -- | inr r => {

  --   cases Ne.lt_or_lt r with
  --   | inl l => {
  --     suffices : Set.InjOn f (Set.Icc a b)
  --     intros ha hb
  --     have crux1 := Inj_inc a b hab f l hf this
  --     have crux2 := neg_deriv_dec f (deriv f a) a ha (by {
  --       have : deriv f a ≠ 0 := by exact LT.lt.ne ha
  --       specialize hf' a
  --       exact hasDerivAt_deriv_iff.mpr hf'
  --     })
  --     match crux2 with
  --     | ⟨δ, hd, Hd⟩ => {
  --       specialize Hd (min (δ / 2) (b - a)) (by {
  --         apply And.intro
  --         {
  --           apply lt_min_iff.mpr
  --           apply And.intro
  --           linarith
  --           linarith
  --         }
  --         apply min_lt_iff.mpr
  --         left
  --         linarith
  --       })
  --       have : a < min (a + δ / 2) b := by {
  --         apply lt_min_iff.mpr
  --         apply And.intro
  --         linarith
  --         exact hab
  --       }
  --       apply crux1 at this
  --       simp only [add_sub_cancel'_right ,← min_add_add_left a (δ / 2) (b - a)] at Hd
  --       linarith
  --       exact Set.left_mem_Icc.mpr (le_of_lt hab)
  --       simp
  --       exact ⟨by linarith, by linarith⟩
  --     }
  --   }
  -- }
#check exists_deriv_eq_zero-- rolles theorem
#check exists_deriv_eq_slope
#check intermediate_value_Icc
