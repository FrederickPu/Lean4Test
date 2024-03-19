import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LHopital

example (x : ℝ) : deriv Real.log x = 1 / x := by norm_num [Real.deriv_log x]

-- Note that in lean Real.log means natural logarithm
-- lim_{x → ∞} ln x = ∞
example : Filter.Tendsto Real.log Filter.atTop Filter.atTop := by {
  exact Real.tendsto_log_atTop
}

#check Filter.EventuallyEq
#check Filter.tendsto_def
example (F1 F2 : Filter ℝ) (f g : ℝ → ℝ): Filter.Tendsto f F1 F2 → f =ᶠ[F1] g → Filter.Tendsto g F1 F2 :=
  fun a a_1 =>
  (fun hl => (Filter.tendsto_congr' hl).mpr)
    (id (Filter.EventuallyEq.symm a_1)) a

#check Metric.ball

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

-- lim_{x → ∞} f (x) / g(x) = lim_{x → ∞} (1 / g (x)) / (1 / f(x)) = (-g'(x) / g(x)^2) / (-f'(x) / f(x)^2)

#check deriv.lhopital_zero_atTop
#check Real.differentiableAt_log
theorem id_beat_log : Filter.Tendsto (fun x => Real.log x / x) Filter.atTop (nhds 0) := by {
  have : (fun x => (1 / x) / (1 / Real.log x)) =ᶠ[Filter.atTop] (fun x => Real.log x / x) := by {
    simp only [Filter.EventuallyEq, Filter.eventually_atTop]
    use 0
    intro b hb
    field_simp
  }
  rw [← Filter.tendsto_congr' this]
  have wow : Filter.Tendsto (fun x => 1 / x) Filter.atTop (nhds (0:ℝ)) := by {
    rw [atTop_nhds]
    intro ε he
    use (2 / ε)
    intro x hx
    have w : 2 / ε > 0 := by {
        have : 2 * (1 / ε) > 0 := by linarith [one_div_pos.mpr he]
        field_simp at this
        exact this
      }
    have : 1 / (2 / ε) ≥ 1 / x := one_div_le_one_div_of_le w hx
    field_simp at this
    simp only [sub_zero]
    rw [abs_of_pos]
    linarith
    have : x > 0 := by linarith
    exact one_div_pos.mpr this
  }
  have wow1 : Filter.Tendsto (fun x => 1 / Real.log x) Filter.atTop (nhds (0:ℝ)) := by {
    have :=  Real.tendsto_log_atTop
    exact Filter.Tendsto.comp wow this
  }
  apply deriv.lhopital_zero_atTop
  simp only [Filter.eventually_atTop]
  use 1
  intro b hb
  have : b ≠ 0 := by linarith
  simp
  exact differentiableAt_inv.mpr this

  simp only [Filter.eventually_atTop]
  use (1 + 1)
  intro b hb
  simp only [one_div]
  rw [deriv_inv'']
  simp only [Real.deriv_log']
  simp only [ne_eq, div_eq_zero_iff, neg_eq_zero, inv_eq_zero, zero_lt_two, pow_eq_zero_iff,
    Real.log_eq_zero, or_self_left]
  simp [not_or]
  exact ⟨by linarith, by linarith, by linarith⟩

  have : b > 0 := by linarith
  exact Real.differentiableAt_log (by linarith)
  have : b > 1 := by linarith
  have : Real.log b > 0 := by exact Real.log_pos this
  linarith
  exact wow
  exact wow1

  -- 1/x^2 / (1 / (ln x)^2 * 1 / x )
  have : (fun x => deriv (fun x => 1 / x) x / deriv (fun x => 1 / Real.log x) x) =ᶠ[Filter.atTop] (fun x => -(x^2)⁻¹ / (- ((Real.log x)^2)⁻¹ * x⁻¹)) := by {
    simp only [Filter.EventuallyEq, Filter.eventually_atTop]
    use (1 + 1)
    intro b hb
    simp
    rw [deriv_inv'']
    simp
    field_simp
    ring
    have : b ≠ 0 := by linarith
    exact Real.differentiableAt_log this
    have : b > 1 := by linarith
    have : Real.log b > 0 := by exact Real.log_pos this
    linarith
  }
  rw [Filter.tendsto_congr' this]

  have : (fun x => -(x^2)⁻¹ / (- (Real.log x^2)⁻¹ * x⁻¹)) =ᶠ[Filter.atTop] (fun x => (Real.log x)^2 / x) := by {
    simp only [Filter.EventuallyEq, Filter.eventually_atTop]
    use 2
    intro b hb
    field_simp
    ring
  }

  rw [Filter.tendsto_congr' this]
}

-- log x / log (x + 1)
