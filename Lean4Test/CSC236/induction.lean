import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic

open Set

inductive trace
| zerozero : trace
| addoneone : trace → trace
| addthreezero : trace → trace

def trace.rep : trace → (ℕ × ℕ)
| zerozero => (0, 0)
| addoneone t => (t.rep.1 + 1, t.rep.2 + 1)
| addthreezero t => (t.rep.1 + 3, t.rep.2)

def S := trace.rep '' Set.univ

def S' := { x : ℕ × ℕ | x.1 ≥ x.2 ∧ 3 ∣ (x.1 - x.2 : ℤ) }

theorem S_subset_S' : S ⊆ S' := by
{
  intro ⟨x, y⟩
  intro ⟨t, h⟩
  induction t generalizing x y with
  | zerozero => {
    rw [← h.2, trace.rep, S']
    simp
  }
  | addoneone t ih => {
    rw [← h.2, trace.rep]
    simp at ih
    specialize ih (x - 1) (y - 1)
    have w := h.2
    simp [trace.rep] at w
    have : trace.rep t = (x - 1, y - 1) := Prod.ext (eq_tsub_of_add_eq w.1) (eq_tsub_of_add_eq w.2)
    specialize ih this
    simp [S'] at ih
    simp [S', this, ih]
  }
  | addthreezero t ih => {
    simp [← h.2, trace.rep]
    simp at ih
    specialize ih (x - 3) y
    have w := h.2
    simp [trace.rep] at w
    have := w.1
    have : trace.rep t = (x - 3, y) := Prod.ext (eq_tsub_of_add_eq w.1) w.2
    specialize ih this
    simp [S'] at ih
    simp [S', this]
    apply And.intro
    linarith [ih.left]
    have : x ≥ 3 := by linarith [w.1]
    have e : (x - 3 : ℕ) = (x - 3 : ℤ) := Int.ofNat_sub this
    have :  (x - 3 + 3 - y : ℤ) = x - y := by ring
    rw [← e] at this
    rw [this]
    have : (x - 3 : ℕ) - y = (x - y : ℤ) - (3:ℕ) := by {
      rw [e]
      ring
    }
    rw [this] at ih
    exact dvd_sub_self_right.mp ih.2
  }
}

#check Nat.strong_induction_on
theorem S'_subset_S : S' ⊆ S := by
{
  suffices : ∀ n : ℕ, ∀ v ∈ S', v.1 + v.2 = n → (v.1, v.2) ∈ S
  {
    intro (x, y) H
    specialize this (x + y) (x, y)
    simp [S] at this
    simp [S]
    apply this
    exact H
  }
  intro n
  let p := fun n => ∀ v ∈ S', v.1 + v.2 = n → (v.1, v.2) ∈ S
  apply @Nat.strong_induction_on p n
  intro n
  intro ih
  simp [p]
  intro a b ⟨t, hab⟩ H
  cases n with
  | zero => {
    have h₁ : a = 0 := Nat.eq_zero_of_add_eq_zero_right H
    have h₂ : b = 0 := Nat.eq_zero_of_add_eq_zero_left H
    simp [h₁, h₂, S]
    use trace.zerozero
    rfl
  }
  | succ n => {
    cases Nat.eq_zero_or_pos b with
    | inl l => {
      simp [l, S]
      simp [l] at hab
      simp only [l] at t
      have : 3 ∣ a := Int.ofNat_dvd.mp hab
      match this with
      | ⟨k, hk⟩ => {
        cases k with
        | zero => {
          simp at hk
          simp [hk]
          exact ⟨trace.zerozero, rfl⟩
        }
        | succ k => {
          specialize ih (3 * k) (by linarith)
          simp [p] at ih
          specialize ih (a - 3) 0
          simp [S', S] at ih
          have : 3 ∣ (a - 3 : ℤ) := dvd_sub_self_right.mpr hab
          have o : (a - 3 : ℤ) = (a - 3 : ℕ) := by {
            have : a ≥ 3 := by linarith
            exact (Int.ofNat_sub this).symm
          }
          rw [o] at this
          specialize ih this (by linarith)
          match ih with
          | ⟨u, hu⟩ => {
            use trace.addthreezero u
            simp [trace.rep, hu]
            exact
              Mathlib.Tactic.Ring.add_congr (congrFun (congrArg HSub.hSub hk) 3) rfl (id hk.symm)
          }
        }
      }
    }
    | inr r => {
      simp at t
      have : a > 0 := by linarith
      specialize ih (a + b - 2) (by {
        rw [H]
        simp
        have : n - 1 ≤ n := Nat.sub_le n 1
        linarith
      })
      simp [p] at ih
      specialize ih (a - 1) (b - 1)
      simp [S, S'] at ih

      have h₁ : (a - 1 : ℤ) = (a - 1 : ℕ) := by exact (Int.ofNat_sub this).symm
      have h₂ : (b - 1 : ℤ) = (b - 1 : ℕ) := (Int.ofNat_sub r).symm

      specialize ih (by linarith [Nat.sub_add_cancel this]) (by {
        rw [← h₁, ← h₂]
        ring_nf
        simp at hab
        exact hab
      }) (by {
        have : (a - 1 : ℕ) + (b - 1 : ℕ) = ((a + b : ℕ) - (2 : ℕ):ℤ) := by {
          rw [← h₁, ← h₂]
          simp
          ring
        }
        have w : ((a - 1 :ℕ) + (b - 1 :ℕ) : ℤ) = ((a - 1) + (b - 1) : ℕ) := by exact rfl
        rw [w] at this
        have w' : ((a + b : ℕ) - (2:ℕ):ℤ) = ((a + b) - 2 : ℕ) := by {
          have : a + b ≥ 2 := by linarith
          exact (Int.ofNat_sub this).symm
        }
        rw [w'] at this
        exact Int.ofNat_inj.mp this
      })
      match ih with
      | ⟨u, hu⟩ => {
        use trace.addoneone u
        simp [trace.rep, hu]
        apply And.intro
        linarith
        linarith
      }
    }
  }
}

example : S = S' :=
  Subset.antisymm S_subset_S' S'_subset_S
