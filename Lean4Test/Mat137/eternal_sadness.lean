import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Asymptotics.Asymptotics

example : (∃ x : ℝ, 2 * x = 1) → False := by
{
  intro w
  match w with
  | ⟨x, hx⟩ => {

  }

}

example (a b : ℕ) : ¬ (a = b) ↔ a ≠ b := by library_search
example (a L : ℝ) (f : ℝ → ℝ) : Filter.Tendsto f (nhdsWithin a {a}ᶜ) (nhds L) → (∀ ε > 0, ∃ δ > (0:ℝ), ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε) := by
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
  w : ∃ x, P(x)
  match w with
  | ⟨x : α, h : P(x)⟩ => {

  }
  match
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

example (a L : ℝ) (f : ℝ → ℝ) : Filter.Tendsto f (nhdsWithin a {a}ᶜ) (nhds L) ↔ (∀ ε > 0, ∃ δ > (0:ℝ), ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε) := by
  apply Iff.intro
  intro h
  intros ε he
  have : {x : ℝ | |x - L| < ε} ∈ nhds L := by {
    rw [mem_nhds_iff]
    use ({x : ℝ | |x - L| < ε})
    simp only [Set.setOf_subset_setOf, imp_self, forall_const, Set.mem_setOf_eq, abs_one,
      true_and]
    exact ⟨Metric.isOpen_ball, by {norm_num; exact he}⟩
  }
  apply h at this
  simp [Filter.map, nhdsWithin] at this
  rw [Filter.mem_inf_iff] at this
  match this with
  | ⟨t1, ht1, t2, ht2, h⟩ => {
    rw [mem_nhds_iff] at ht1
    match ht1 with
    | ⟨t, ⟨ht, ht', ht''⟩⟩ => {
      simp at ht2
      rw [Metric.isOpen_iff] at ht'
      specialize ht' a ht''
      match ht' with
      | ⟨δ, hd, Hd⟩ => {
        use δ; use hd
        intros x hx
        have crux1 : x ∈ Metric.ball a δ := hx.right
        have crux2 : x ∈ {(a:ℝ)}ᶜ := by {
          have : x ∉ {(a:ℝ)} := by {
            intro h
            rw [Set.mem_singleton_iff] at h
            simp [h] at hx
          }
          exact Set.mem_compl this
        }
        have : x ∈ t1 ∩ t2 := Set.mem_inter (ht (Hd crux1)) (ht2 crux2)
        rw [← h] at this
        exact this
      }
    }
  }
  intro h
  intros E hE
  simp only [Filter.mem_map]
  rw [mem_nhds_iff] at hE
  match hE with
  | ⟨t, ht, hO, HL⟩ => {
    rw [Metric.isOpen_iff] at hO
    specialize hO L HL
    match hO with
    | ⟨ε, he, He⟩ => {
      simp only [nhdsWithin, Filter.mem_inf_iff]
      apply h at he
      match he with
      | ⟨δ, hd, Hd⟩ => {
        have : {x | |x - a| < δ} ∈ nhds a := by {
          rw [mem_nhds_iff]
          use {x | |x - a| < δ}
          simp only [Set.setOf_subset_setOf, imp_self, forall_const, Set.mem_setOf_eq, sub_self,
            abs_zero, true_and]
          exact ⟨Metric.isOpen_ball, hd⟩
        }
        use {x | |x - a| < δ}
        use this
        use {x | 0 < |x - a|}
        apply And.intro
        simp
        intros x hx
        simp
        simp at hx
        exact sub_ne_zero.mpr hx
        have : {x | |x - a| < δ} ∩ {x | 0 < |x - a|} = {x | 0 < |x - a| ∧ |x - a| < δ} := by {
          exact Set.setOf_inter_eq_sep (fun a_1 => |a_1 - a| < δ) {x | 0 < |x - a|}
        }
        rw [this]
        ext x

      }
    }
  }

#check Metric.isOpen_iff
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : HasDerivAt f 1 0 → ∃ ε > 0, |2 / ε * (f (ε / 2) - f 0) - 2| < 2:= by
{
  intros hfd
  rw [hasDerivAt_iff_tendsto_slope_zero] at hfd
  have : {x : ℝ | |x - 2| < 2} ∈ nhds 1 := by {
    rw [mem_nhds_iff]
    use ({x : ℝ | |x - 2| < 2} )
    simp only [Set.setOf_subset_setOf, imp_self, forall_const, Set.mem_setOf_eq, abs_one,
      true_and]
    apply And.intro
    exact Metric.isOpen_ball -- very important
    norm_num
  }
  specialize hfd this
  simp [Filter.map, nhdsWithin] at hfd
  rw [Filter.mem_inf_iff] at hfd
  match hfd with
  | ⟨t1, ht1, t2, ht2, h⟩ => {
    rw [mem_nhds_iff] at ht1
    match ht1 with
    | ⟨t, ⟨ht, ht', ht''⟩⟩ => {
      simp at ht2
      rw [Metric.isOpen_iff] at ht'
      specialize ht' 0 ht''
      match ht' with
      | ⟨ε, he, He⟩ => {
        have crux : Metric.ball 0 ε ⊆ t1 := Set.Subset.trans He ht
        have crux1 : ε / 2 ∈ Metric.ball 0 ε := by {
          simp
          have : |ε| = ε := by exact abs_of_pos he
          rw [this]
          linarith
        }
        have crux2 : ε/2 ∈ {(0:ℝ)}ᶜ := by {
          have : ε/2 ∉ {(0:ℝ)} := by {
            intro h
            rw [Set.mem_singleton_iff] at h
            linarith
          }
          exact Set.mem_compl this
        }
        have := ht2 crux2
        have := ht <| He crux1
        have : ε/2 ∈ t1 ∩ t2 := Set.mem_inter (ht (He crux1)) (ht2 crux2)
        rw [← h] at this
        simp at this
        use ε
      }
    }
  }
}

example (a b : ℝ) (hb : b > 0): |a| < b → -b < a ∧ a < b := by {
  intro h
  exact abs_lt.mp h
}

theorem pos_deriv_inc (f : ℝ → ℝ) : ∀ f' > 0, HasDerivAt f f' 0 → ∃ ε > 0, ∀ x > 0, x < ε → f 0 < f x := by
{
  intros f' hp hfd
  rw [hasDerivAt_iff_tendsto_slope_zero] at hfd
  have : {x : ℝ | |x - f'| < f'} ∈ nhds f' := by {
    rw [mem_nhds_iff]
    use ({x : ℝ | |x - f'| < f'} )
    simp only [Set.setOf_subset_setOf, imp_self, forall_const, Set.mem_setOf_eq, abs_one,
      true_and]
    apply And.intro
    exact Metric.isOpen_ball -- very important
    norm_num
    linarith
  }
  specialize hfd this
  simp [Filter.map, nhdsWithin] at hfd
  rw [Filter.mem_inf_iff] at hfd
  match hfd with
  | ⟨t1, ht1, t2, ht2, h⟩ => {
    rw [mem_nhds_iff] at ht1
    match ht1 with
    | ⟨t, ⟨ht, ht', ht''⟩⟩ => {
      simp at ht2
      rw [Metric.isOpen_iff] at ht'
      specialize ht' 0 ht''
      match ht' with
      | ⟨ε, he, He⟩ => {
        have crux : Metric.ball 0 ε ⊆ t1 := Set.Subset.trans He ht
        simp at this
        use ε
        use he
        intros x hx hxe
        have crux1 : x ∈ Metric.ball 0 ε := by {
          simp
          have : |x| = x := by exact abs_of_pos hx
          rw [this]
          linarith
        }
        have crux2 : x ∈ {(0:ℝ)}ᶜ := by {
          have : x ∉ {(0:ℝ)} := by {
            intro h
            rw [Set.mem_singleton_iff] at h
            linarith
          }
          exact Set.mem_compl this
        }
        have := ht2 crux2
        have := ht <| He crux1
        have : x ∈ t1 ∩ t2 := by exact Set.mem_inter (ht (He crux1)) (ht2 crux2)
        rw [← h] at this
        simp at this
        rw [abs_lt] at this
        have := this.left
        norm_num at this
        have : x*0 < x *(x⁻¹ *(f x - f 0)) := by exact (mul_lt_mul_left hx).mpr this
        rw [← mul_assoc] at this
        rw [mul_inv_cancel crux2] at this
        linarith
      }
    }
  }
}

theorem neg_deriv_dec (f : ℝ → ℝ) : ∀ f' < 0, HasDerivAt f f' 0 → ∃ ε > 0, ∀ x > 0, x < ε → f 0 > f x := by
{
  intros f' hp hfd
  rw [hasDerivAt_iff_tendsto_slope_zero] at hfd
  have : {x : ℝ | |x - f'| < -f'} ∈ nhds (f') := by {
    rw [mem_nhds_iff]
    use ({x : ℝ | |x - f'| < -f'} )
    simp only [Set.setOf_subset_setOf, imp_self, forall_const, Set.mem_setOf_eq, abs_one,
      true_and]
    apply And.intro
    exact Metric.isOpen_ball -- very important
    norm_num
    exact hp
  }
  specialize hfd this
  simp [Filter.map, nhdsWithin] at hfd
  rw [Filter.mem_inf_iff] at hfd
  match hfd with
  | ⟨t1, ht1, t2, ht2, h⟩ => {
    rw [mem_nhds_iff] at ht1
    match ht1 with
    | ⟨t, ⟨ht, ht', ht''⟩⟩ => {
      simp at ht2
      rw [Metric.isOpen_iff] at ht'
      specialize ht' 0 ht''
      match ht' with
      | ⟨ε, he, He⟩ => {
        have crux : Metric.ball 0 ε ⊆ t1 := Set.Subset.trans He ht
        simp at this
        use ε
        use he
        intros x hx hxe
        have crux1 : x ∈ Metric.ball 0 ε := by {
          simp
          have : |x| = x := by exact abs_of_pos hx
          rw [this]
          linarith
        }
        have crux2 : x ∈ {(0:ℝ)}ᶜ := by {
          have : x ∉ {(0:ℝ)} := by {
            intro h
            rw [Set.mem_singleton_iff] at h
            linarith
          }
          exact Set.mem_compl this
        }
        have := ht2 crux2
        have := ht <| He crux1
        have : x ∈ t1 ∩ t2 := by exact Set.mem_inter (ht (He crux1)) (ht2 crux2)
        rw [← h] at this
        simp at this
        rw [abs_lt] at this
        have := this.right
        have : x⁻¹ * (f x - f 0) < 0 := by linarith
        have : x * (x⁻¹ * (f x - f 0)) < x * 0 := by exact (mul_lt_mul_left hx).mpr this
        rw [← mul_assoc] at this
        rw [mul_inv_cancel crux2] at this
        linarith only [this]
      }
    }
  }
}
