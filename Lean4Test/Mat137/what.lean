import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Int.Log
import Mathlib.Tactic

#check Real.mk
#check Finset.sum

#check IsCauSeq
#check Real.log
#check Int.log

-- ((1/2)^n - 1) / (1 / 2)=  1 / 2^(n-1) - 2
#check Nat.pow
theorem two_geo_series (n : ℕ) : (Finset.sum (Finset.range n) fun i => 1 / 2 ^ (i.succ) : ℚ) = - 1 / 2^n+ 1 := by {
  induction n with
  | zero => rfl
  | succ n hn => {
    rw [Finset.sum_range_succ]
    rw [hn]
    have : (2 : ℚ) > 0 := by linarith
    have : (2:ℚ)^n > 0 := by exact pow_pos this n
    rw [pow_succ]
    field_simp
    ring
  }
}


example (n : ℕ) (f g : ℕ → ℚ) (h : ∀ i ∈ Finset.range n, 0 ≤ f i) : 0 ≤ Finset.sum (Finset.range n) f := by {
  exact Finset.sum_nonneg h
}
example (n : ℕ) (f g : ℕ → ℚ) (h : ∀ i ∈ Finset.range n, f i ≤ g i) : Finset.sum (Finset.range n) f ≤ Finset.sum (Finset.range n) g := by {
  exact Finset.sum_le_sum h
}

#check div_le_div_right
example (a b c : ℚ) (h : c > 0) : a ≤ b → a / c ≤ b / c := by library_search

example (n : ℕ) (s : Finset ℕ) (f : ℕ → Fin 2) : Finset.sum s (fun i => (f i) / (2 : ℚ) ^ i) ≤ (Finset.sum s (fun i => 1 / (2:ℚ) ^ i)) := by {
  apply Finset.sum_le_sum
  intro i _
  suffices w : (f i:ℕ) ≤ 1
  have : (2)^i > 0 := Nat.pow_two_pos i
  have q : (2^i : ℚ) > 0 := by exact pow_pos (by linarith) i
  have : (f i:ℚ) ≤ 1 := by exact Nat.cast_le_one.mpr w
  exact (div_le_div_right q).mpr this

  linarith [(f i).isLt]
}

example (n : ℕ) (f : ℕ → Fin 2) : (Finset.sum (List.toFinset (List.range n)) fun i => (f i) / (2 : ℚ) ^ i) ≤ (Finset.sum (List.toFinset (List.range n)) fun i => 1 / (2:ℚ) ^ i) := by {
  apply Finset.sum_le_sum
  intro i _
  suffices w : (f i:ℕ) ≤ 1
  have : (2)^i > 0 := Nat.pow_two_pos i
  have q : (2^i : ℚ) > 0 := by exact pow_pos (by linarith) i
  have : (f i:ℚ) ≤ 1 := by exact Nat.cast_le_one.mpr w
  exact (div_le_div_right q).mpr this

  linarith [(f i).isLt]
}

#check Finset.Ico
#check Nat.Ico_succ_singleton
#check Nat.Ico_succ_right_eq_insert_Ico
#check Nat.image_sub_const_Ico
theorem Ico_split (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : Finset.Ico a b ∪ Finset.Ico b c = Finset.Ico a c := by {
  ext x
  simp
  apply Iff.intro
  intro h
  cases h with
  | inl l => {
    apply And.intro
    linarith [l]
    linarith
  }
  | inr r => {
    apply And.intro
    linarith [r]
    linarith
  }

  intro h
  have : x < b ∨ b ≤ x := by exact Nat.lt_or_ge x b
  tauto
}

theorem Ico_eq_range (n m : ℕ) (hm : n ≤ m) : Finset.Ico n m = Finset.range m \ Finset.range n := by
{
  have crux : Finset.range n ∪ Finset.Ico n m = Finset.range m := by {
    rw [← Nat.Ico_zero_eq_range]
    rw [Ico_split]
    exact Nat.zero_le n
    exact hm
  }
  have : Disjoint (Finset.range n) (Finset.Ico n m) := by {
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    ext x
    simp
    intro h1 h2
    linarith
  }
  exact (Disjoint.sdiff_eq_of_sup_eq this crux).symm
}
theorem Ico_sum (f : ℕ → ℚ) (n m : ℕ) (hm : n ≤ m) : Finset.sum (Finset.range m) f - Finset.sum (Finset.range n) f = Finset.sum (Finset.Ico n m) f := by {
  rw [Ico_eq_range]
  have : Finset.range n ⊆ Finset.range m := by {
    intro x
    simp
    intro h
    linarith
  }
  rw [← Finset.sum_sdiff this]
  simp only [Finset.range_subset, add_sub_cancel]
  linarith
}

#check Nat.pow_log_le_self
#check Int.log
example (a : ℕ) (ha : a ≠ 0) : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 ha
example (a b : ℕ) : a ≤ b → (a : ℚ) ≤ (b : ℚ) := by {
  intro H
  exact Nat.cast_le.mpr H
}
example : (ℕ → Fin 2) ↪ ℝ :=
  ⟨fun f => by {
    apply Real.mk
    exact ⟨fun n => Finset.sum (Finset.range n) (fun i => (f i)/(2 ^ (i+1))), by {
      intro ε he
      use (- Int.log (2:ℕ) ε).toNat
      intro j hj
      simp
      rw [Ico_sum]
        -- apply Finset.sum_le_sum

      have : (Finset.sum (Finset.Ico (- Int.log (2:ℕ) ε).toNat j) fun i => (f i) / (2:ℚ) ^ (i+1)) ≤ Finset.sum (Finset.Ico (- Int.log (2:ℕ) ε).toNat j) fun i => 1 / (2:ℚ) ^ (i+1) := by {
        apply Finset.sum_le_sum
        intro i hi

        suffices w : (f i:ℕ) ≤ 1
        have : (2)^(i+1) > 0 := Nat.pow_two_pos (i+1)
        have q : (2^(i+1) : ℚ) > 0 := by exact pow_pos (by linarith) (i+1)
        have : (f i:ℚ) ≤ 1 := by exact Nat.cast_le_one.mpr w
        exact (div_le_div_right q).mpr this

        linarith [(f i).isLt]
      }
      rw [abs_of_nonneg]
      suffices : Finset.sum (Finset.Ico (- Int.log (2:ℕ) ε).toNat j) (fun i => (1 / (2:ℚ) ^ (i+1))) < ε
      linarith
      rw [← Ico_sum, two_geo_series, two_geo_series]

      wlog h : ε ≥ 1
      simp at h
      have : Int.log 2 ε < 0 := by {
        have hb : 2 > 1 := by linarith
        have hx : ε < (2:ℚ)^0 := by simp; exact h
        exact (Int.lt_zpow_iff_log_lt hb he).mp hx
      }
      calc
         _ = 1 / (2:ℚ) ^ (- Int.log (2:ℕ) ε).toNat- 1 / (2:ℚ) ^ j := by ring
        _ = (2:ℚ) ^ Int.log (2:ℕ) ε - 1 / (2:ℚ) ^ j  := by {
          have crux : Int.toNat (-Int.log 2 ε) = -Int.log 2 ε := by {
            apply Int.toNat_of_nonneg
            linarith only [this]
          }
          have : (2 : ℚ) ^ (Int.toNat (-Int.log 2 ε) : ℕ) = (2 : ℚ) ^ (Int.toNat (-Int.log 2 ε) : ℤ) := by exact rfl
          rw [this, crux]
          simp
        }
        _ ≤  ε - 1 / (2:ℚ) ^ j := by {
          have : (2:ℚ) ^ Int.log (2:ℕ) ε ≤ ε := Int.zpow_log_le_self (by linarith) he
          linarith
        }
        _ < ε := by {
          have : (2:ℚ) ^ j > 0 := by exact pow_pos (by rfl) j
          have : 1 / (2:ℚ) ^ j  > 0 := by exact one_div_pos.mpr this
          linarith
        }
      have : (-Int.log 2 ε) ≤ 0 := by {sorry}
      have : Int.toNat (-Int.log 2 ε) = 0 := by exact Int.toNat_eq_zero.mpr this
      rw [this]
      simp
      have : (2:ℚ) ^ j > 0 := by exact pow_pos (by rfl) j
      have : 1 / (2:ℚ) ^ j  > 0 := by exact one_div_pos.mpr this
      have : -(1 / (2:ℚ) ^ j) < 0 := by linarith
      have : -(1 / (2:ℚ) ^ j)  = -1 / (2:ℚ) ^ j := by exact neg_div' (2 ^ j) 1
      linarith

      exact hj
      apply Finset.sum_nonneg
      intro i hi
      apply div_nonneg
      have : ((f i) : ℕ)≥ ((0:Fin 2) : ℕ) := by exact Fin.zero_le (f i)
      exact Nat.cast_le.mpr this
      exact le_of_lt <| pow_pos (by rfl) (i+1)
      exact hj
    }⟩
  }, by {}⟩
