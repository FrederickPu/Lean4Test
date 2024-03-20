import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Tactic


#check abs (10:ℝ)
#check Int.toNat
def kevin (n : Nat) (factor : ℚ) : Nat := Int.toNat <| if factor < 0 then (n - Int.ceil (n * |factor|)) else (n + Int.ceil (n * |factor|))
def fred (n : Nat) (factor : ℚ) : Nat := Int.toNat <| if factor ≥ 0 then Int.ceil (n*(1 + factor)) else Int.floor (n*(1 + factor))

example (n : Nat) (factor : ℚ) : kevin n factor = fred n factor := by {
  simp only [kevin, fred]
  cases em (factor ≥ 0) with
  | inl l => {
    rw [abs_of_nonneg l]
    have : ¬ factor < 0 := by exact not_lt.mpr l
    simp only [l, ite_true, this, ite_false]
    ring
    have : Int.ceil (↑n + ↑n * factor) = n + Int.ceil (n * factor) := by {
      rw [add_comm, Int.ceil_add_nat (n * factor) n]
      ring
    }
    rw [this]
  }
  | inr r => {
    simp only [r, ite_false]
    simp at r
    simp only [r, ite_true]
    rw [abs_of_neg r]
    have : Int.ceil (↑n * -factor) = - Int.floor (n * factor) := by {
      have : Int.ceil (-(n * factor)) = - Int.floor ((n * factor)) := Int.ceil_neg
      simp [this]
    }
    rw [this]
    apply congrArg
    ring_nf
    rw [add_comm, ← Int.floor_add_nat (n * factor) n]
    ring
  }
}
