import Mathlib.RingTheory.Bezout
#check IsBezout.gcd_eq_sum

example (x y : ℤ) : ∃ a b, a*x + b*y = IsBezout.gcd x y :=
IsBezout.gcd_eq_sum x y

example (a b c : ℤ) : (∃ x y : ℤ, a*x + b*y = c) ↔ IsBezout.gcd a b ∣ c := by
  apply Iff.intro
  exact fun ⟨x, y, h⟩ => by
    match IsBezout.gcd_dvd_left a b, IsBezout.gcd_dvd_right a b with
    | ⟨d, hd⟩, ⟨e, he⟩ =>
      have : IsBezout.gcd a b * (d*x + e*y) = c := by
        ring_nf
        rw [← hd, ← he]
        exact h
      use (d * x + e * y)
      exact this.symm
  exact fun ⟨k, h⟩ => by
    match IsBezout.gcd_eq_sum a b with
    | ⟨x, y, h1⟩ =>
      rw [← h1] at h
      use (k*x)
      use (k*y)
      linear_combination -h
example (x y : ℤ) : 19 ∣ 3*x + 7*y → 19 ∣ 43*x + 75*y := by
  intro ⟨k, h⟩
  have crux : 3*x = (19*k - 7*y) := eq_sub_of_add_eq h
  have : 43 * x + 75 * y = 19 * (2*x + 4*y) + (5*x - y) := by ring
  rw [this]
  suffices : 19 ∣ 5*x - y
  exact Int.dvd_add ⟨2*x + 4*y, rfl⟩ this
  suffices : 19 ∣ 3*(5*x - y)
  exact Int.dvd_of_dvd_mul_right_of_gcd_one this rfl
  use 5*k - 2*y
  linarith

#check Nat.gcd_eq_iff
#check Nat.lcm_eq_iff
example (a b : ℕ) : a*b = lcm a b * gcd a b := by
{


}

open Nat
example (m n : Nat) : Nat.gcd m n * Nat.lcm m n = m * n := by
  rw [Nat.lcm, Nat.mul_div_cancel' (Nat.dvd_trans (Nat.gcd_dvd_left m n) (Nat.dvd_mul_right m n))]
