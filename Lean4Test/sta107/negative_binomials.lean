import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic



example (n : Nat): (Finset.sum (Finset.range (n + 1)) fun m => (Nat.choose n m)) = 2^n := by {
  have : Commute 1 1  := by rfl
  have := Commute.add_pow this n
  ring_nf at this
  rw [this]
  simp
  rw [add_comm]
}

example (n : ℕ) (x : ℝ) (hx : x ≠ 0): (1 - x)^(n + 1) * ∑' (k : ℕ), Nat.choose (k + n) n * x^k = 1 := by
{

}
example (n : ℕ) : 1 / (1 - x) ^ (n + 1) = ∑' (k : ℕ), Nat.choose (k + n) n * x^k := by
{
  sorry
}
