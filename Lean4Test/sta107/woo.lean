import Mathlib.Data.Real.Basic
import Mathlib.Algebra.DualNumber
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.TrivSqZeroExt



#check DualNumber ℝ

example (x : ℝ) : x^2 = x*x := by exact sq x
example (x : DualNumber ℝ) : ((x + DualNumber.eps)^2 - x^2)  = 2 * x * DualNumber.eps := by {
  ring_nf
  simp only [add_right_eq_self]
  rw [sq]
  exact DualNumber.eps_mul_eps
}

#check add_sub_cancel'


example (n : Nat) : Nat.choose (n + 1) n = n+1 := by library_search

theorem tsum_snd (f : Nat → DualNumber ℝ) (hf : ∀ n, TrivSqZeroExt.fst (f n) = 0) : tsum (fun x => TrivSqZeroExt.snd (f x)) = TrivSqZeroExt.snd (tsum f) := by sorry

theorem diff_pow (x : ℝ) (n : Nat): ((TrivSqZeroExt.inl x) + DualNumber.eps : DualNumber ℝ)^(n + 1)  - ((TrivSqZeroExt.inl x)^(n+1)) =  ((TrivSqZeroExt.inl x)^(n) * DualNumber.eps * ((n + 1) : DualNumber ℝ)) := by
{
  have : Commute (TrivSqZeroExt.inl x) DualNumber.eps := DualNumber.commute_eps_right (TrivSqZeroExt.inl x)
  have w := Commute.add_pow this (n+1)
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at w
  suffices : (fun i : Nat => (TrivSqZeroExt.inl x) ^ i * (DualNumber.eps ^ (n + 1 - i)) * (Nat.choose (n + 1) i : DualNumber ℝ))  = (fun i => (TrivSqZeroExt.inl 0 : DualNumber ℝ))
  have :   (Finset.sum (Finset.range n) fun i =>
        (TrivSqZeroExt.inl x) ^ i * DualNumber.eps ^ (n + 1 - i) * ↑(Nat.choose (n + 1) i : DualNumber ℝ)) = (Finset.sum  (Finset.range n) (fun i => (TrivSqZeroExt.inl 0 : DualNumber ℝ))) := by
  {
    apply congrArg
    exact this
  }
  rw [this, Finset.sum_eq_zero, Nat.add_sub_self_left n 1, Nat.sub_self] at w
  rw [pow_one, pow_zero, Nat.choose_self] at w
  rw [w]
  rw [Nat.choose_succ_self_right n]
  rw [pow_succ]
  push_cast
  ring

  intro x hx
  simp
  {
    ext i
    sorry
    sorry
  }

}
example (x : ℝ) : (∑' (n : Nat), n * x^n) = x * TrivSqZeroExt.snd (∑' (n : Nat), (((TrivSqZeroExt.inl x) + DualNumber.eps : DualNumber ℝ)^n  - (TrivSqZeroExt.inl x)^n)) := by {
  calc
    _ = (∑' (n : Nat), x * (n * x^(n - 1))) := by {
      apply congrArg
      ext n
      cases n with
      | zero => {
        simp
      }
      | succ n => {
        simp
        rw [Nat.succ_eq_add_one]
        ring
      }
    }
    _ = x * (∑' (n : Nat), n * x^(n - 1)) := by {
      rw [tsum_mul_left]
    }
    _ = x * TrivSqZeroExt.snd (∑' (n : Nat), (((TrivSqZeroExt.inl x) + DualNumber.eps : DualNumber ℝ)^n  - (TrivSqZeroExt.inl x)^n)) := by {
      apply congrArg
      calc
        ∑' (n : ℕ), ↑n * x ^ (n - 1) =  ∑' (n : Nat), (TrivSqZeroExt.snd <| ((TrivSqZeroExt.inl x) + DualNumber.eps : DualNumber ℝ)^(n)  - ((TrivSqZeroExt.inl x)^(n))) := by {
          apply congrArg
          ext n
          cases n with
          | zero => {
            simp
          }
          | succ n => {
            rw [Nat.succ_eq_add_one, Nat.add_sub_self_right n 1]
            rw [diff_pow x n]
            simp
            ring
          }
        }
        _ = TrivSqZeroExt.snd (∑' (n : Nat), (((TrivSqZeroExt.inl x) + DualNumber.eps : DualNumber ℝ)^(n)  - ((TrivSqZeroExt.inl x)^(n)))) := by {
          rw [tsum_snd]

          intro n
          cases n with
          | zero => simp
          | succ n =>
            rw [Nat.succ_eq_add_one, diff_pow]
            simp
        }
    }
}

-- ε^2 = 0
-- a * (b + c) = a*b + a*c
-- a*b = b*a

-- (a + b ε) * (c + d ε) = a c + adε + bc ε + bdε^2
-- ac + (ad + bc)ε + bd * 0
-- ac + (ad + bc)ε

--  ((x + ε)^2 - x^2)/ε = f'(x)
-- ((x + ε)^2 - x^2) = f'(x)ε
-- (x + ε)^2 - x^2 = x^2 + 2εx + ε^2 - x^2 = 2εx + 0 = (2x)ε
-- x^n -> nx^(n - 1)
-- (x + ε)^n = x^n + nx^(n - 1)ε + 0 + 0 + 0
-- (a + bε) / (c + dε) = (a + bε) (c - dε) / (c^2)

-- ∑ deriv x^n = deriv ∑ x^n
-- ∑ ((x + ε)^n - x^n) / ε = 1 / ε ∑ ((x + ε)^n - x^n)


noncomputable instance : Div (DualNumber ℝ) :=
{
  div := fun ⟨a, b⟩ ⟨c, d⟩ => ⟨a/c, (b*c - a*d)/c^2⟩
}

#check HMul
instance {F : Type*} [Field F] : Field (DualNumber F) :=
{
  inv := fun ⟨a, b⟩ => ⟨1 / a, (-b)/a^2⟩
  exists_pair_ne := by {
    have : ∃ a b : F, a ≠ b := exists_pair_ne F
    match this with
    | ⟨a, b, H⟩ => {
      use ⟨a, 0⟩
      use ⟨b, 0⟩
      intro h
      have : (a, (0:F)).fst = (b, (0:F)).fst := by exact congrArg Prod.fst h
      exact H this
    }
  }
  mul_inv_cancel := fun (⟨a, b⟩ : DualNumber F) hxy => by {
    simp [HMul.hMul, Mul.mul]
    -- `a` may be 0 even though `(a, b) ≠ 0`
    -- ie `(a, b) = (0, 1)`
    -- in this case the (a, b) * (a, b)⁻¹ = 0 which is a contradiction
    -- so DualNumber are not a field
  }

}

example (x : ℝ) : (∑' (n : Nat), (((TrivSqZeroExt.inl x) + DualNumber.eps : DualNumber ℝ)^n  - (TrivSqZeroExt.inl x)^n)) =  1 / (1 - ((TrivSqZeroExt.inl x + DualNumber.eps))) - 1 / (1 - TrivSqZeroExt.inl x) := by
  calc
    _ = (∑' (n : Nat), (((TrivSqZeroExt.inl x) + DualNumber.eps : DualNumber ℝ)^n ) - (∑' (n : Nat), (TrivSqZeroExt.inl x)^n)) := by {
      apply tsum_sub
      sorry
      sorry
    }
    _ = _ := by {
      apply congr
      apply congrArg
      sorry
      sorry
    }
  -- TrivSqZeroExt.fst

example : 1 / (1 - ((TrivSqZeroExt.inl x + DualNumber.eps))) - 1 / (1 - TrivSqZeroExt.inl x : DualNumber ℝ) = ((TrivSqZeroExt.inl x + DualNumber.eps) - TrivSqZeroExt.inl x) / ((1 - ((TrivSqZeroExt.inl x + DualNumber.eps))) * (1 - TrivSqZeroExt.inl x)) := by
{

}

#check TrivSqZeroExt.instTopologicalSpace
