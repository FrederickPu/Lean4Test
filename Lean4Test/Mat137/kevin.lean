import Mathlib
import Mathlib.Tactic

def is_odd (x : ℤ) : Prop :=
  ∃ (k : ℤ), x = 2 * k + 1

theorem two_odd_even (x y: ℤ) (a1: is_odd x) (a2: is_odd y): ∃ (k : ℤ), x + y = 2 * k := by{
  match a1, a2 with
  |  ⟨k1, a1⟩, ⟨k2, a2⟩ =>
    use k1 + k2 + 1
    rw [a1, a2]
    ring
}
