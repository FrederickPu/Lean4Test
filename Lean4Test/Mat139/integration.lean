import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic

-- import Mathlib.MeasureTheory.Integral.IntervalIntegral

#check @HPow.hPow ℝ ℕ ℝ instHPow Real.pi (2:ℕ)


-- (a : α) ^[β] (b : β) = @HPow.hPoq α β α instHPow a b
notation:80 x " ^[" N:50 "] " n:50 => @HPow.hPow _ N _ instHPow x n

#check 2 ^ 10
#check Real.pi ^[ℕ] (2:ℕ)

example (a b : ℝ) (hab : a ≤ b) (ha : a > 0) :
  (∫ x : ℝ in a..b, Real.log x / x)  = (Real.log b ^ 2 - Real.log a ^ 2) / 2  := by {
    have : (fun x => Real.log x / x) = fun x =>  x⁻¹ * Real.log x:= by {
      ext x
      ring
    }
    have w3 : ContinuousOn (fun x => x⁻¹) (Set.uIcc a b) := by {
      have : ContinuousOn (fun x :ℝ => x) (Set.uIcc a b) := continuousOn_id
      apply ContinuousOn.inv₀ this
      intro x hx
      simp
      rw [Set.uIcc_of_le hab] at hx
      linarith [hx.left]
    }
    have w1 : ∀ x ∈ Set.uIcc a b, HasDerivAt Real.log x⁻¹ x := by {
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have : x > 0 := by linarith [hx.left]
      exact Real.hasDerivAt_log (ne_of_gt this)
    }
    rw [this]
    have := intervalIntegral.integral_comp_smul_deriv' w1 w3 continuousOn_id
    simp at this
    rw [this]
    simp
  }

#check (Real.pi)^(1)
example (T : ℕ → ℝ) (h : ∀ n : ℕ, T n = (∫ x : ℝ in (0:ℝ)..(2*Real.pi), (Real.cos x)^[ℕ] ((2*n):ℕ))) :
  ∀ n, T (n + 1) = (2*n + 1 : ℕ) * T n - (2 * n + 1) * T (n + 1) := by {
  intro n
  calc
    T (n + 1) = (∫ x : ℝ in (0:ℝ)..(2*Real.pi), (Real.cos x)^[ℕ](2*(n+1):ℕ)) := by rw [h (n + 1)]
    _ =  ∫ (x : ℝ) in (0:ℝ)..(2*Real.pi), ((Real.cos x)^[ℕ] (2*n + 1 : ℕ)) * Real.cos x := by {
      apply congr
      apply congrArg (fun x => intervalIntegral x 0 (2*Real.pi))
      ext x
      ring
      rfl
    }
    _ =  ((Real.cos (2*Real.pi))^[ℕ](2*n + 1 : ℕ)) * Real.sin (2*Real.pi)  -  ((Real.cos 0) ^[ℕ] (2*n + 1 : ℕ)) * Real.sin 0  - ∫ (x : ℝ) in (0:ℝ)..(2*Real.pi), ((2*n + 1 : ℕ) * ((Real.cos x) ^[ℕ](2*n)) * (- Real.sin x)) * Real.sin x := by {
      have hu : ∀ x ∈ Set.uIcc 0 (2*Real.pi), HasDerivAt (fun x => (Real.cos (x))^[ℕ] (2*n + 1 : ℕ)) ((2*n + 1 :ℕ) * ((Real.cos x) ^[ℕ] (2*n)) * (- Real.sin x)) x := by {
        intro x _
        have hh : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
        have hh2 : HasDerivAt (fun x:ℝ => x^[ℕ] (2*n + 1 : ℕ)) ((2*n + 1:ℕ)*(Real.cos x)^[ℕ](2*n:ℕ)) (Real.cos x):= by {
          have := hasDerivAt_pow (2*n + 1) (Real.cos x)
          simp at this
          simp
          exact this
        }
        have := HasDerivAt.comp x hh2 hh
        simp [Function.comp] at this
        simp [this]
      }
      have hv : ∀ x ∈ Set.uIcc 0 (2*Real.pi), HasDerivAt Real.sin (Real.cos x) x := by {
        intro x _
        exact Real.hasDerivAt_sin x
      }
      have hu' : IntervalIntegrable (fun x => ((2*n + 1:ℕ)*(Real.cos x)^[ℕ](2*n:ℕ)) * -Real.sin x) MeasureTheory.volume 0 (2 * Real.pi) := by {
        have : Continuous (fun x:ℝ => (Real.cos x) ^[ℕ] (2 * n)) := by exact Continuous.comp (continuous_pow (2 * n)) Real.continuous_cos
        have : Continuous (fun x : ℝ => ↑(2 * n + 1) • (Real.cos x) ^[ℕ] (2 * n)) := Continuous.const_smul this ↑(2 * n + 1)
        simp only [nsmul_eq_mul] at this
        apply Continuous.intervalIntegrable
        apply Continuous.mul
        exact this
        apply Continuous.neg
        exact Real.continuous_sin
      }
      have hv' : IntervalIntegrable Real.cos MeasureTheory.volume 0 (2 * Real.pi) := by {
        have : Continuous Real.cos := Real.continuous_cos
        apply Continuous.intervalIntegrable
        exact this
      }
      have := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
      exact this
    }
    _ =  ((Real.cos (2*Real.pi))^[ℕ](2*n + 1 : ℕ)) * Real.sin (2*Real.pi)  -  ((Real.cos 0) ^[ℕ] (2*n + 1 : ℕ)) * Real.sin 0  - (2*n + 1 : ℕ) * ∫ (x : ℝ) in (0:ℝ)..(2*Real.pi), ((Real.cos x) ^[ℕ](2*n)) * (- Real.sin x) * Real.sin x := by {
     have : (fun x :ℝ => ↑(2 * n + 1:ℕ) * ((Real.cos x) ^[ℕ] (2 * n)) * -Real.sin x * Real.sin x) = (fun x => ↑(2 * n + 1 :ℕ) * (((Real.cos x) ^[ℕ] (2 * n)) * -Real.sin x * Real.sin x)) := by
        ext x
        ring
     rw [this]
     have :  (∫ (x : ℝ) in (0:ℝ)..(2 * Real.pi), (2 * n + 1 :ℕ) * (((Real.cos x) ^[ℕ] (2 * n)) * -Real.sin x * Real.sin x)) = (2*n + 1 : ℕ) * ∫ (x : ℝ) in (0:ℝ)..(2*Real.pi), ((Real.cos x) ^[ℕ](2*n)) * (- Real.sin x) * Real.sin x := by
      apply intervalIntegral.integral_const_mul
     rw [this]
    }
    _ = (2*n + 1 : ℕ) * T n - (2 * n + 1) * T (n + 1) := by {
      have : (fun x:ℝ => ((Real.cos x) ^[ℕ](2*n)) * (- Real.sin x) * Real.sin x) = (fun x:ℝ => - (((Real.cos x) ^[ℕ](2*n)) * ((Real.sin x) ^[ℕ] 2))) := by
        ext x
        ring
      rw [this, intervalIntegral.integral_neg]
      have : (fun (x : ℝ) => ((Real.cos x) ^[ℕ](2*n)) * (Real.sin x) ^[ℕ] 2) = (fun (x : ℝ) => (((Real.cos x) ^[ℕ] (2*n)) -((Real.cos x) ^[ℕ] 2*(n+1)))) := by
        ext x
        rw [Real.sin_sq]
        ring
      rw [this]
      simp
      rw [intervalIntegral.integral_sub]
      rw [← h n, ← h (n + 1)]
      ring

      apply Continuous.intervalIntegrable
      exact Continuous.comp (continuous_pow (2 * n)) Real.continuous_cos
      apply Continuous.intervalIntegrable
      exact Continuous.comp (continuous_pow (2 * (n+1))) Real.continuous_cos
    }
}

#check Real.hasDerivAt_arcsin
example (a b : ℝ) (hab : a ≤ b) (ha : 0 < a) (hb : b < 1) : (∫ x in a..b, 1 / Real.sqrt (1 - x^2)) = Real.arcsin  b - Real.arcsin a := by {
  have : (fun x => 1 / Real.sqrt (1 - x^2)) = (fun x => deriv Real.arcsin x) := by {
    rw [Real.deriv_arcsin]
    simp
  }
  rw [this]
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
  exact hab
  apply Continuous.continuousOn
  exact Real.continuous_arcsin
  intro x hx
  apply HasDerivAt.hasDerivWithinAt
  simp only [Real.deriv_arcsin]
  apply Real.hasDerivAt_arcsin
  linarith [hx.left]
  linarith [hx.right]

  have : ContDiffOn ℝ 1 Real.arcsin ({-1, 1}ᶜ) := Real.contDiffOn_arcsin
  have : ContDiffOn ℝ 1 Real.arcsin (Set.uIcc a b) := by sorry
  have : ContinuousOn (deriv Real.arcsin) (Set.uIcc a b) := by {
    apply ContDiffOn.continuousOn_deriv_of_isOpen

  }
}
#check integral_eq_sub_of_hasDeriv_right_of_le
#check intervalIntegral.integral_sub
#check congr_fun
#check HasDerivAt.comp -- chain rule
#check intervalIntegral.integral_mul_deriv_eq_deriv_mul
#check intervalIntegral.integral_comp_smul_deriv'
#check Real.log_continuousOn
#check ContinuousOn.mono
#check Lean.Expr

-- ∫ (x : ℝ) in a..b, f' x • (g ∘ f) x = ∫ (u : ℝ) in f a..f b, g u

-- good reference for theorems: https://leanprover-community.github.io/undergrad.html
