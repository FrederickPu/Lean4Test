import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Parity



def limit (a : ℕ → ℝ) (L : ℝ) := ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n > N → |a n - L| < ε

example (a : ℕ → ℝ) (L : ℝ) : limit a L → limit (fun n => a (2*n + 1)) L := by
  intro h
  intro ε he
  specialize h ε he
  match h with
  | ⟨N, h⟩ => {
    use N
    intro n hn
    have : 2*n + 1 > N := by linarith
    specialize h (2*n+1) this
    exact h
  }

example (a : ℕ → ℝ) (L : ℝ) : limit a L → limit (fun n => a (n + 1) - a n) 0 := by
{
  intro h
  intro ε he
  specialize h (ε/2) (half_pos he)
  match h with
  | ⟨N, hN⟩ => {
    use N
    intro n hn
    have w := hN n hn
    have w1 := hN (n+1) (by linarith)
    simp only [sub_zero]
    have := abs_add (a (n + 1) - L) (L - a n)
    rw [← abs_sub_comm (a n) L] at this
    simp at this
    linarith
  }
}

def decreasing (a : ℕ → ℝ) := ∀ n m : ℕ, n < m → a n > a m
def increasing (a : ℕ → ℝ) := ∀ n m : ℕ, n < m → a n < a m
def bounded (a : ℕ → ℝ) := ∃ A B : ℝ, ∀ n, A ≤ a n ∧ a n ≤ B
def jumpy (a : ℕ → ℝ) := ∀ n, a n * a (n + 1) < 0
def wobbly (a : ℕ → ℝ) := jumpy (fun n => a (n + 1) - a n)

theorem limit_unique (a : ℕ → ℝ) (L1 L2 : ℝ) : limit a L1 → limit a L2 → L1 = L2 := by {
  intro h1 h2
  have : ∀ ε > 0, |L1 - L2| < ε := by {
    intro ε he
    specialize h1 (ε / 2) (half_pos he)
    specialize h2 (ε / 2) (half_pos he)
    match h1, h2 with
    | ⟨N1, hN1⟩, ⟨N2, hN2⟩ => {
      specialize hN1 (max N1 N2 + 1) (by linarith [Nat.le_max_left N1 N2])
      specialize hN2 (max N1 N2 + 1) (by linarith [Nat.le_max_right N1 N2])
      have : |a (max N1 N2 + 1) - L1| = |L1 - a (max N1 N2 + 1)| := abs_sub_comm (a (max N1 N2 + 1)) L1
      rw [this] at hN1
      have := abs_add (L1 - a (max N1 N2 + 1)) (a (max N1 N2 + 1) - L2)
      simp at this
      linarith
    }
  }
  have : |L1 - L2| ≤ 0 := by exact le_of_forall_lt' this
  have : L1 - L2 = 0 := abs_nonpos_iff.mp this
  linear_combination this
}

theorem inc_bounded_converge (a : ℕ → ℝ) : increasing a → bounded a → ∃ L, limit a L := by
{
  intro h_inc h_bound
  use sSup (a '' Set.univ)
  intro ε he
  have hee : BddAbove (a '' Set.univ) := by {
    simp [BddAbove, Set.Nonempty]
    match h_bound with
    | ⟨M, N, h⟩ => {
      use N
      simp [upperBounds]
      intro n
      specialize h n
      exact h.right
    }
  }
  have wee : (a '' Set.univ).Nonempty := by {
    use a 1
    simp only [Set.image_univ, Set.mem_range, exists_apply_eq_apply]
  }
  have := Real.add_neg_lt_sSup wee (neg_lt_zero.mpr he)
  match this with
  | ⟨u, ⟨⟨N, hN⟩, ha⟩⟩ => {
    rw [← hN.right] at ha
    simp at ha
    simp
    use N
    intro n hn
    specialize h_inc N n hn
    have : a n ≤ sSup (Set.range a) := by {
      rw [Real.le_sSup_iff]
      intro w hw
      use a n
      simp
      exact hw
      simp at hee
      exact hee
      simp at wee
      exact wee
    }
    have : a n - sSup (Set.range a) ≤ 0 := by linarith
    rw [abs_of_nonpos this]
    linarith
  }
}
theorem dec_bounded_converge (a : ℕ → ℝ) : decreasing a → bounded a → ∃ L, limit a L := by
{
  intro h_inc h_bound
  use sInf (a '' Set.univ)
  intro ε he
  have hee : BddBelow (a '' Set.univ) := by {
    simp [BddBelow, Set.Nonempty]
    match h_bound with
    | ⟨M, N, h⟩ => {
      use M
      simp [lowerBounds]
      intro n
      specialize h n
      exact h.left
    }
  }
  have wee : (a '' Set.univ).Nonempty := by {
    use a 1
    simp only [Set.image_univ, Set.mem_range, exists_apply_eq_apply]
  }
  have := Real.lt_sInf_add_pos wee (he)
  match this with
  | ⟨u, ⟨⟨N, hN⟩, ha⟩⟩ => {
    rw [← hN.right] at ha
    simp at ha
    simp
    use N
    intro n hn
    specialize h_inc N n hn
    have : sInf (Set.range a) ≤ a n := by {
      rw [Real.sInf_le_iff]
      intro w hw
      use a n
      simp
      exact hw
      simp at hee
      exact hee
      simp at wee
      exact wee
    }
    have : a n - sInf (Set.range a) ≥ 0 := by linarith
    rw [abs_of_nonneg this]
    linarith
  }
}

theorem limit_diff (a b : ℕ → ℝ) (L R : ℝ) : limit a L → limit b R → limit (fun n => a n - b n) (L - R) := by {
  intro hL
  intro hR
  intro ε he
  specialize hL (ε / 2) (half_pos he)
  specialize hR (ε / 2) (half_pos he)
  match hL, hR with
  | ⟨N1, hN1⟩, ⟨N2, hN2⟩ => {
    use max N1 N2
    intro n hn
    specialize hN1 n (by linarith [Nat.le_max_left N1 N2])
    specialize hN2 n (by linarith [Nat.le_max_right N1 N2])
    have := abs_add (a n - L) (R - b n)
    rw [abs_sub_comm R (b n)] at this
    have w : a n - L + (R - b n) = a n - b n - (L - R) := by ring
    rw [w] at this
    simp only
    linarith
  }
}
variables (a A : ℕ → ℝ) (hA: ∀ n, A n = a (n + 1) - a n) (h1 : wobbly a) (h2 : limit A 0) (h3 : decreasing (fun n => |A n|)) (h4 : A 1 > 0)
example : A = fun n => a (n + 1) - a n:= by
  ext n
  exact hA n

theorem lemma1 : ∀ n, A (2*n + 1) > 0 ∧ A (2*n) < 0
| 0 => by {
  use h4
  simp
  have := h1 0
  simp only at this
  rw [← hA 0, ← hA 1] at this
  exact (neg_iff_pos_of_mul_neg this).mpr h4
}
| Nat.succ n => by {
  have := lemma1 n
  have crux1 := h1 (2*n + 1)
  simp only at crux1
  rw [← hA (2*n + 1), ← hA (2*n + 2)] at crux1

  rw [Nat.succ_eq_add_one]
  ring
  have crux2 := h1 (2*n + 2)
  simp only at crux2
  rw [← hA (2*n + 2), ← hA (2*n + 3)] at crux2
  have w : A (2*n + 2) < 0 := by exact (pos_iff_neg_of_mul_neg crux1).mp this.left
  have w1 : A (2*n + 3) > 0 := by exact (neg_iff_pos_of_mul_neg crux2).mp w

  rw [add_comm, mul_comm] at w1
  rw [add_comm, mul_comm] at w
  exact ⟨w1, w⟩
}

theorem dec_lem : ∀ n, a (2*n) > a (2*(n + 1)) := by {
  intro n
  -- 2n, 2n + 1, 2n + 2
  have := h3 (2*n) (2*n + 1) (by linarith)
  simp at this
  have crux := lemma1 a A hA h1 h4 n
  rw [abs_of_neg crux.right, abs_of_pos crux.left] at this
  rw [hA (2*n), hA (2*n + 1)] at this
  have : a (2*n + 1 + 1) < a (2*n) := by linarith
  ring_nf at this
  ring_nf
  exact this
}

theorem even_dec : decreasing (fun n => a (2 * n)) := by
{
  intro n m
  induction m with
  | zero => simp
  | succ m h => {
    intro hnm
    have : n ≤ m := by exact Nat.lt_succ.mp hnm
    cases Nat.lt_or_eq_of_le this with
    | inl l => {
      specialize h l
      have := dec_lem a A hA h1 h3 h4 m
      simp only
      rw [Nat.succ_eq_add_one]
      linarith
    }
    | inr r => {
      rw [r]
      simp
      rw [Nat.succ_eq_add_one]
      exact dec_lem a A hA h1 h3 h4 m
    }
  }
}

theorem inc_lem : ∀ n, a (2*n + 1) < a (2*(n + 1) + 1) := by {
  intro n
  --2n + 1, 2n + 2, 2n + 3
  have := h3 (2*n + 1) (2*n + 2) (by linarith)
  simp at this
  have crux1 := lemma1 a A hA h1 h4 n
  have crux2 := lemma1 a A hA h1 h4 (n + 1)
  rw [abs_of_pos crux1.left] at this
  ring_nf at crux2
  ring_nf at this
  rw [abs_of_neg crux2.right] at this
  rw [hA (2 + n*2), hA (1 + n*2)] at this
  ring_nf at this
  ring_nf
  linarith
}

theorem odd_inc : increasing (fun n => a (2*n + 1)) := by {
  intro n m
  induction m with
  | zero => simp
  | succ m h => {
    intro hnm
    have : n ≤ m := by exact Nat.lt_succ.mp hnm
    cases Nat.lt_or_eq_of_le this with
    | inl l => {
      specialize h l
      have := inc_lem a A hA h1 h3 h4 m
      simp only
      rw [Nat.succ_eq_add_one]
      linarith
    }
    | inr r => {
      rw [r]
      simp
      rw [Nat.succ_eq_add_one]
      exact inc_lem a A hA h1 h3 h4 m
    }
  }
}

theorem even_bounded : bounded (fun n => a (2*(n+1))) := by {
  use a 1; use a 2
  intro n
  simp only
  apply And.intro
  have := lemma1 a A hA h1 h4
  specialize this (n + 1)
  have := this.right
  rw [hA (2*(n+1))] at this
  have := odd_inc a A hA h1 h3 h4 0 (n + 1) (by linarith)
  simp only at this
  ring_nf at *
  linarith

  cases LE.le.gt_or_eq (Nat.le_add_left 1 n) with
  | inl l => {
    have := even_dec a A hA h1 h3 h4 1 (n+1) l
    simp only at this
    ring_nf at *
    linarith
  }
  | inr r => {
    rw [r]
  }
}


theorem odd_bounded : bounded (fun n => a (2*n + 1)) := by {
  use a 1; use a 2
  intro n
  simp only
  apply And.intro
  cases LE.le.gt_or_eq (Nat.zero_le n) with
  | inl l => {
    have := odd_inc a A hA h1 h3 h4 0 n l
    simp at this
    linarith
  }
  | inr r => {
    rw [r]
  }

  have := lemma1 a A hA h1 h4 n
  have := this.left
  rw [hA (2*n + 1)] at this
  cases LE.le.gt_or_eq (Nat.le_add_left 1 n) with
  | inl l => {
    have := even_dec a A hA h1 h3 h4 1 (n + 1) l
    simp at this
    ring_nf at *
    linarith
  }
  | inr r => {
    have w : 2 * n + 1 + 1 = 2 := by linarith
    rw [w] at this
    linarith
  }
}

theorem A_odd_converges : limit (fun n => A (2*n + 1)) 0 := by {
  intro ε he
  simp
  specialize h2 ε he
  match h2 with
  | ⟨N1, hN1⟩ => {
    use N1 + 1
    intro n hn
    specialize hN1 (2*n + 1) (by linarith)
    simp at hN1
    exact hN1
  }
}

theorem even_odd_converge : ∃ L, limit (fun n => a (2*n + 1)) L ∧ limit (fun n => a (2*(n+1))) L := by {
  have w := odd_inc a A hA h1 h3 h4
  have w1 := odd_bounded a A hA h1 h3 h4
  have crux := inc_bounded_converge (fun n => a (2*n + 1)) w w1
  have q := even_dec a A hA h1 h3 h4
  have q1 := even_bounded a A hA h1 h3 h4
  have crux1 := dec_bounded_converge  (fun n => a (2*(n+1))) (by {
    intro n m
    intro hnm
    have := even_dec a A hA h1 h3 h4 (n + 1) (m + 1) (by linarith)
    exact this
  }) q1
  have woop := A_odd_converges A h2
  have w : (fun n => A (2*n + 1)) = fun n => a (2*(n+1)) - a (2*n + 1) := by {
    ext n
    rw [hA (2*n+1)]
    ring
  }
  rw [w] at woop
  match crux, crux1 with
  | ⟨L_odd, hodd⟩, ⟨L_even, heven⟩ => {
    have := limit_diff (fun n => a (2*(n+1))) (fun n => a (2*n + 1)) L_even L_odd heven hodd
    simp only at this
    have := limit_unique (fun n => a (2*(n + 1)) - a (2*n + 1)) 0 (L_even - L_odd) woop this
    use L_odd
    have h : L_even = L_odd := by linarith
    apply And.intro
    exact hodd
    rw [← h]
    exact heven
  }
}

example :  ∃ L, (limit (fun n => a (2*n + 1)) L ∧ limit (fun n => a (2*(n+1))) L) ∧ limit a L := by {
  have := even_odd_converge a A hA h1 h2 h3 h4
  match this with
  | ⟨L, hL⟩ => {
    use L
    use hL
    intro ε he
    have w := hL.left ε he
    have w1 := hL.right ε he
    match w, w1 with
    | ⟨N1, hN1⟩, ⟨N2, hN2⟩ => {
      use max (2*N1 + 1) (2*N2) + 2
      intro n hN

      cases Nat.even_or_odd n with
      | inl l => {
        have : ∃ k, n = 2*k := Even.exists_two_nsmul n l
        match this with
        | ⟨k, hk⟩ => {
          have : n ≥ 1 := by linarith [Nat.le_max_left (2*N1 + 1) (2*N2)]
          cases k with
          | zero => {
            linarith
          }
          | succ k => {
            specialize hN2 k (by linarith [Nat.le_max_right (2*N1 + 1) (2*N2)])
            simp at hN2
            rw [← hk] at hN2
            exact hN2
          }
        }
      }
      | inr r => {
        have : ∃ k, n = 2*k + 1 := by exact r
        match this with
        | ⟨k, hk⟩ => {
          specialize hN1 k (by linarith [Nat.le_max_left (2*N1 + 1) (2*N2)])
          simp only at hN1
          rw [← hk] at hN1
          exact hN1
        }
      }
    }
  }
}
