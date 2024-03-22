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

#eval String.join ["hello", "mark"]
#check List.join
def List.join' {α : Type} (x : α): List (List α) → List α
| nil => nil
| a :: nil => a ++ nil
| a :: b :: l => a ++ [x] ++ b ++ l.join' x

theorem List.bruh {α : Type} (x a : α) (A : List α) : (L : List (List α)) → List.join' x ((a::A)::L) = a :: List.join' x (A::L)
| nil => by simp [join']
| B :: nil => by simp [join']
| A :: B :: L => by simp [join']

theorem wow : (l : List Nat) → (∀ n, n ∈ l → ∃ L : List (List Nat), (∀ x ∈ L, n ∉ x) ∧ (L.join' n = l))
| List.nil => by {
  intro n hn
  simp at hn
}
| a :: List.nil => by {
  intro n hn
  simp at hn
  rw [hn]
  use [[], []]
  simp [List.join']
}
| a :: l => by {
  intro n hn
  cases em (n = a) with
  | inl hn1 => {
    cases em (n ∈ l) with
    | inl H => {
      have := wow l n H
      match this with
      | ⟨L, hh⟩ => {
        match L with
        | List.nil => {
          use []::[[]]
          simp [List.join'] at hh
          simp [List.join']
          simp [hn1, hh]
        }
        | A :: L => {
          use []::[]::A::L
          simp [List.join', hh]
          simp at hh
          use hh.left.right
        }
      }
    }
    | inr H => {
      simp [H] at hn
      simp [hn]
      use []::[]::l::[]
      simp [List.join']
      rw [← hn1]
      exact H
    }
  }
  | inr hn2 => {
    cases em (n ∈ l) with
    | inl H => {
      have := wow l n H
      match this with
      | ⟨L, HL⟩ => {
        match L with
        | A :: L => {
          use (a::A)::L
          simp [hn2, HL]
          simp at HL
          use HL.left.right
          simp [List.bruh]
          exact HL.right
        }
        | List.nil => {
          simp [List.join'] at HL
          use [a]::List.nil
          rw [← HL]
          simp [List.join']
          exact hn2
        }
      }
    }
    | inr H => {
      use (a::l)::[]
      simp [List.join', hn2, H]
    }
  }
}

theorem duh : (l : List Nat)  → ∀ n, n ∈ l → ∃ a b : List Nat, l = a ++ [n] ++ b
| List.nil => by {
  intro n hn
  simp at hn
}
| List.cons x l => by {
  have := duh l
  intro n hn
  simp at hn
  cases hn with
  | inl hl => {
    use []
    use l
    simp
    exact hl.symm
  }
  | inr hr => {
    specialize this n hr
    match this with
    | ⟨a, b, H⟩ => {
      use x :: a
      use b
      simp [H]
    }
  }
}
