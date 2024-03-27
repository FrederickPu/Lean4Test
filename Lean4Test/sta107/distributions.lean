import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Analysis.Calculus.Series
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv



#check Commute.add_pow

example (n : Nat): (Finset.sum (Finset.range (n + 1)) fun m => (Nat.choose n m)) = 2^n := by {
  have : Commute 1 1  := by rfl
  have := Commute.add_pow this n
  ring_nf at this
  rw [this]
  simp
  rw [add_comm]
}

example (f g : Nat → Nat) : (∀ n, f n = g n) → f = g := by library_search
theorem binomial_dist (n : Nat) {F : Type} [Field F] (p : F) :  (Finset.sum (Finset.range (n + 1)) (fun m => p^m*(1-p)^(n -m) *(Nat.choose n m))) = 1 := by
{
  have : Commute p (1 - p) := Commute.all p (1 - p)
  have w := Commute.add_pow this n
  ring_nf at this
  have : (fun m => p^m*(1-p)^(n -m) *(Nat.choose n m)) = (fun m => p ^ m * (1 - p) ^ (n - m) * ↑(Nat.choose n m)) := by
    ext m
    ring
  rw [this]
  rw [← w]
  ring
}

example (r : NNReal) (hr : r < 1) : ∑' (n : ℕ), (1 - r) * r ^ n = 1 := by {
  have w := tsum_geometric_nnreal hr
  have : (1 - r) * ∑' (n : ℕ), r ^ n  = ∑' (n : ℕ), (1 - r) * r ^ n := by exact
    (NNReal.tsum_mul_left (1 - r) fun x => r ^ x).symm
  rw [← this, w]
  have : 1 - r > 0 := tsub_pos_of_lt hr
  have : 1 - r ≠ 0 := zero_lt_iff.mp this
  exact mul_inv_cancel this
}


theorem Nat.choose_def (n k : Nat) : Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
  by rfl

example (a : ℝ) : a⁻¹ = 1 / a := by exact inv_eq_one_div a

example (p: NNReal) (hp0: 0 < p) (hp1: p < 1) :
  ∑' (n : ℕ), ↑n * (1 - p) ^ n * p = 0 := by {

  }

#check Finset.sum
example (a b c : ℝ) : a + b + c = a + c + b := by
{
  exact add_right_comm a b c
}

#check tsum_mul_left
theorem HockeyStick : (k r : Nat) → (Finset.range (k + 1)).sum (fun i => Nat.choose (i + r) r) = Nat.choose (k + r + 1) (r + 1)
| 0, r => by simp
| k + 1, r => by
  rw [Finset.sum_range_succ]
  rw [HockeyStick k r]
  rw [add_right_comm k 1 r, add_comm]
  exact rfl

example (x : ℝ) (f g : ℝ → ℝ) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  f =ᶠ[nhds x] g → deriv f x = deriv g x := by exact fun a => Filter.EventuallyEq.deriv_eq a
theorem bruh (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : (r : ℕ) →
  (∑' (n : ℕ), Nat.choose (n + r) (r) * (1 - p) ^ n * p^(r+1) = 1)
 | 0 => by {
  have : (fun n => ↑(Nat.choose (n + 0) 0) * (1 - p) ^ n * p ^ (0 + 1)) =  fun n => p * (1 - p) ^ n   := by
    ext n
    simp [Nat.choose]
    ring
  rw [this, tsum_mul_left]

  have hp1': 1 - p < 1 := by linarith
  have hp0' : 0 ≤ 1 - p := by linarith
  rw [tsum_geometric_of_lt_1 hp0' hp1']
  have : 1 - (1 - p) = p :=
    tsub_tsub_cancel_of_le (le_of_lt hp1)
  rw [this]
  apply mul_inv_cancel
  linarith
}
 | Nat.succ r => by {
  have crux :  ∑' (n : ℕ), (Nat.choose (n + r) (r+1) * (1 - p) ^ n) = (1 - p) * (p^(r + 2))⁻¹ := by
  {
    calc
      _ = ∑' (n : ℕ), (n / (r + 1:ℕ) * Nat.choose (n + r) r * (1 - p) ^ n) := by {
        apply congrArg
        ext n
        have : (r + 1 : ℝ) ≠ 0 := by linarith
        field_simp only
        rw [mul_right_comm, ← Nat.cast_mul]
        rw [Nat.choose_succ_right_eq]
        simp [add_tsub_cancel_right]
        left
        ring
      }
      _ = (1 - p) / (r + 1) * ∑' (n : ℕ), Nat.choose (n + r) r * (n * (1 - p) ^ (n - 1)) := by {
        rw [← tsum_mul_left]
        apply congrArg
        ext n
        cases n with
        | zero => simp
        | succ n => {
          rw [pow_succ]
          simp
          ring
        }
      }
      _ =  (1 - p) / (r + 1) * ∑' (n : ℕ), (-1)*deriv (fun p:ℝ => Nat.choose (n + r) r * (1 - p) ^ n) p := by {
        apply congrArg
        apply congrArg
        ext n
        have h2: DifferentiableAt ℝ (fun p:ℝ => p^n) (1-p:ℝ) := differentiableAt_pow n
        have h: DifferentiableAt ℝ (fun p:ℝ => 1 - p) p := by
         rw [differentiableAt_const_sub_iff]
         exact differentiableAt_id'

        -- have h : deriv (fun p:ℝ => 1 - p) p = -1 := by
        --   rw [deriv_const_sub]
        --   simp only [deriv_id'']
        have := deriv.comp p h2 h
        simp at this
        rw [deriv_const_sub, deriv_id''] at this
        simp only [Function.comp] at this
        rw [deriv_const_mul, this]
        ring

        exact DifferentiableAt.comp p h2 h
      }
      _ =  (1 - p) / (r + 1) * (-1) * ∑' (n : ℕ), deriv (fun p:ℝ => Nat.choose (n + r) r * (1 - p) ^ n) p := by {
      rw [tsum_mul_left]
      ring
     }
      _ = (1 - p) / (r + 1) * (-1) * deriv (fun p:ℝ => (∑' (n : ℕ), Nat.choose (n + r) r * (1 - p) ^ n)) p := by {
      apply congrArg
      sorry
     }
      _ = (1 - p) / (r + 1) * (-1) * deriv (fun p:ℝ => (1 / p^(r + 1))) p := by {
      apply congrArg

      apply Filter.EventuallyEq.deriv_eq
      simp [Filter.EventuallyEq]
      rw [eventually_nhds_iff]
      -- |1/2 - p| < ε => -ε < 1/2 - p < ε => 1/2 - ε < p < 1/2 + ε
      -- 1 / 2 - ε  = 1 / 2 - 1/ 2 = 0
      -- 1/2 + ε = 1/ 2 + 1/ 2= 1
      use Metric.ball (1 / 2) (1 / 2)
      apply And.intro
      intro x hx
      simp only [Metric.ball, dist, Set.mem_setOf_eq] at hx
      rw [abs_sub_lt_iff] at hx
      have := bruh x (by linarith [hx.left]) (by linarith [hx.right]) r
      rw [tsum_mul_right] at this
      have w : x ≠ 0 := by linarith [hx.left, hx.right]
      field_simp
      rw [this]

      apply And.intro
      exact Metric.isOpen_ball
      simp only [Metric.ball, dist, Set.mem_setOf_eq]
      rw [abs_sub_lt_iff]
      apply And.intro
      linarith
      linarith
     }
      _ = (1 - p) / (r + 1) * (-1) * (-(r+1) * (p^(r + 2))⁻¹) := by {
      apply congrArg
      have : (fun p:ℝ => 1 / p ^ (r + 1)) = (fun p:ℝ => (p ^ (r + 1))⁻¹) := by
        ext x
        rw [← inv_eq_one_div]
      rw [this, deriv_inv'', deriv_pow]
      simp
      field_simp
      ring

      exact differentiableAt_pow (r + 1)
      have : p ≠ 0 := by linarith
      exact pow_ne_zero (r + 1) this
    }
      _ = (1 - p) * (p^(r + 2))⁻¹ := by field_simp; ring
  }
  calc
    _ = ∑' (n : ℕ), (Nat.choose (n + r + 1) (r + 1)) * (1 - p) ^ n * p ^ (r + 1 + 1) := by {
      apply congrArg
      ext n
      rw [Nat.succ_eq_add_one, ← add_assoc]
    }
    _ = ∑' (n : ℕ), (Nat.choose (n + r) r + Nat.choose (n + r) (r+1) :ℕ) * (1 - p) ^ n * p ^ (r + 1 + 1) := by {
      simp [Nat.choose]
    }
    _ = ∑' (n : ℕ), (Nat.choose (n + r) r * (1 - p) ^ n * p ^ (r + 1 + 1) + Nat.choose (n + r) (r+1) * (1 - p) ^ n * p ^ (r + 1 + 1)) := by {
      apply congrArg
      ext n
      push_cast
      ring
    }
    _ = p * ∑' (n : ℕ), (Nat.choose (n + r) r * (1 - p) ^ n * p ^ (r+1)) + p ^ (r + 1 + 1) * ∑' (n : ℕ), (Nat.choose (n + r) (r+1) * (1 - p) ^ n) := by {
      rw [← tsum_mul_left, ← tsum_mul_left]
      rw [← tsum_add]
      apply congrArg
      ext n
      push_cast
      ring

      apply Summable.mul_left
      have := bruh p hp0 hp1 r
      apply by_contradiction
      intro h
      simp [tsum_def, h] at this

      apply Summable.mul_left
      apply by_contradiction
      intro h
      simp [tsum_def, h] at crux

      cases crux with
      | inl l => linarith
      | inr r => linarith
    }
    _ = p * ∑' (n : ℕ), (Nat.choose (n + r) r * (1 - p) ^ n * p ^ (r+1)) + p ^ (r + 1 + 1) * ((1 - p) * (p^(r + 2))⁻¹) := by {
      rw [crux]
    }
    _ = 1 := by {
      rw [bruh p hp0 hp1 r]
      have : p ≠ 0 := by linarith
      field_simp
      ring
    }

}

theorem bruh_cope (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1)  : (r : ℕ) →
  ((∑' (n : ℕ), Nat.choose (n + r) (r) * (1 - p) ^ n * p^(r+1) = 1)
  ∧
  (∑' (n : ℕ), n * Nat.choose (n + r) (r) * (1 - p) ^ n * p^(r+1) = (r+1) * (1 - p) / p))
| 0 => by {
  apply And.intro
  have : (fun n => ↑(Nat.choose (n + 0) 0) * (1 - p) ^ n * p ^ (0 + 1)) =  fun n => p * (1 - p) ^ n   := by
    ext n
    simp [Nat.choose]
    ring
  rw [this]
  rw [(NNReal.tsum_mul_left p fun x => (1 - p) ^ x)]

  have : 1 - p < 1 := tsub_lt_self (by norm_num) hp0
  rw [tsum_geometric_nnreal this]
  have : 1 - (1 - p) = p :=
    tsub_tsub_cancel_of_le (le_of_lt hp1)
  rw [this]
  exact mul_inv_cancel <| zero_lt_iff.mp hp0

  simp only [add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, zero_add, pow_one,
    Nat.cast_zero, zero_div]

  calc
     ∑' (n : ℕ), ↑n * (1 - p) ^ n * p = ∑' (n : ℕ), (1 - p) * p * (↑n * (1 - p) ^ (n - 1)) := by
      apply congrArg
      ext n
      cases n with
      | zero => simp
      | succ n =>
        simp
        rw [pow_succ]
        ring
     _ = ∑' (n : ℕ), (deriv (fun (p:ℝ) => -(1 - p) ^ n) p).toNNReal * (1 - p) * p := by
     {
      apply congrArg
      ext n
      have : deriv (fun p:ℝ => -(1 - p) ^ n) p = n * (1 - p : ℝ) ^ (n - 1) := by {
        have woo : deriv (fun x:ℝ => 1 - x) (p:ℝ) = -1 := by
          rw [deriv_const_sub, deriv_id'']
        have : deriv (fun p:ℝ => p ^ n) (1 - p) = n * (1 - p : ℝ) ^ (n - 1) := deriv_pow n
        have hh2 : DifferentiableAt ℝ (fun p:ℝ => (p:ℝ) ^ n) ((fun p :ℝ => 1 - p) (p:ℝ)):= by
          exact differentiableAt_pow n
        have hh : DifferentiableAt ℝ (fun p:ℝ => 1 - (p:ℝ)) p := by
          apply DifferentiableAt.const_sub
          exact differentiableAt_id'
        have : deriv ((fun p:ℝ => p^n) ∘ (fun p => 1 - p)) (p:ℝ) = deriv (fun p:ℝ => p^n) ((fun p:ℝ => 1 - p) p) * deriv (fun p:ℝ => 1 - p) (p:ℝ) := by
          apply deriv.comp
          exact hh2
          exact hh
        have w : ((fun p:ℝ => p ^ n) ∘ (fun p:ℝ => 1 - p)) = (fun p:ℝ => (1 - p)^n) := by
          ext p
          simp
        rw [w] at this
        rw [deriv.neg]
        rw [this]
        simp [woo]
      }
      rw [this]
      ring_nf
      have : n * (1 - p:ℝ) ^ (n - 1) = (n * (1 - p) ^ (n - 1):NNReal).toReal := by {
        have : p ≤ 1 := by sorry
        have : (1 - p : NNReal) = (1 - p:ℝ) := NNReal.coe_sub this
        have w : ((1 - p)^(n - 1): NNReal) = ((1 - p)^(n-1) : ℝ) := by rfl
        have : (n * (1 - p)^(n-1) : NNReal) = ((n:ℝ) * ((1 - (p : ℝ))^(n-1):ℝ) : ℝ) := by {
          rw [← this]
          apply NNReal.coe_mul
        }
        rw [this]
      }
      rw [this, Real.toNNReal_coe]
      apply congrArg
      ring
     }
     _ = ∑' (n : ℕ), ((1 - p) * p) * (deriv (fun (p:ℝ) => -(1 - p) ^ n) p).toNNReal := by
      apply congrArg
      ext n
      push_cast
      ring
     _ = ((1 - p) * p)  * ∑' (n : ℕ), (deriv (fun (p:ℝ) => -(1 - p) ^ n) p).toNNReal := by
      rw [NNReal.tsum_mul_left ((1 - p)*p) _]
     _ = ((1 - p) * p)  * (deriv (fun (p:ℝ) => ∑' (n : ℕ), -(1 - p) ^ n) p).toNNReal := by
      let f := fun (n : ℕ) (p : ℝ)  => -(1 - p)^n
      have : (fderiv ℝ (fun p:ℝ => ∑' (n : ℕ), f n p)) = (fun p => ∑' (n : ℕ), fderiv ℝ (fun p:ℝ => f n p) p)  := by {
        sorry
        -- apply fderiv_tsum
      }
      simp [deriv]
      rw [this]
      simp [f]
      rw [NNReal.tsum_eq_toNNReal_tsum]
      --deriv_tsum

}
| Nat.succ r => by {
  sorry
  -- calc
  --   ∑' (n : ℕ), ↑(Nat.choose (n + Nat.succ r) (Nat.succ r)) * (1 - p) ^ n * p ^ (Nat.succ r + 1) = ∑' (n : ℕ),  (Nat.choose (n+r) r + Nat.choose (n+r) (r + 1)) * (1 - p) ^ n * p ^ Nat.succ (Nat.succ r) := by
  --     apply congrArg
  --     ext n
  --     rw [Nat.add_succ, Nat.choose_def]
  --     simp
  --   _ = ∑' (n : ℕ),  (p * (Nat.choose (n+r) r * (1 - p)^n * p^(r + 1)) + (1 - p) ^ n * p ^ Nat.succ (Nat.succ r) * n / (r + 1) * (Nat.choose (n+r) (r + 1))) := by -- Nat.choose_succ_right_eq
  --     apply congrArg
  --     ext n
  --     simp
  --     rw [Nat.succ_eq_add_one]
  --     ring

}

#check Polynomial.derivative_pow
#check fderiv_tsum
#check Nat.choose_succ_right_eq
