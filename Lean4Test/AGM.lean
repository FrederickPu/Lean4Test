import Mathlib.Tactic
-- import Mathlib.Util.PiNotation

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

-- b lies inside the line segment a1a2 on the real line
def Bet (a1 b a2 : ℝ) := a1 ≤ b ∧ b ≤ a2 ∨ a2 ≤ b ∧  b ≤ a1

theorem Bet.symm {a1 b a2}  : Bet a1 b a2 → Bet a2 b a1 := by
simp [Bet]
tauto

theorem mul_ge_one_imp (a b : ℝ) (ha : a ≥ 0) : a*b ≥ 1 → a ≥ 1 ∨ b ≥ 1 := by
  intro hab
  apply by_contradiction
  intro h
  have := not_or.mp h
  simp at this
  have : b ≤ 1 := by linarith
  have : a*b ≤ a*1 := by exact mul_le_mul_of_nonneg_left this ha
  linarith
theorem mul_le_one_imp (a b : ℝ) (ha : a ≥ 0) : a*b ≤ 1 → a ≤ 1 ∨ b ≤ 1 := by
  intro hab
  apply by_contradiction
  intro h
  have := not_or.mp h
  simp at this
  have : b ≥ 1 := by linarith
  have : a*b ≥ a*1 := by exact mul_le_mul_of_nonneg_left this ha
  linarith

theorem prod_gt_one : (l : List ℝ) → (hl : l.length > 0) → (h1 : ∀ i : Fin l.length, l.get i > 1) → l.prod > 1
| [] => by simp
| [a] => by simp
| (a :: b :: l) => by {
  simp
  intro h1
  have := prod_gt_one (b :: l) (by simp) (by {
    intro i
    specialize h1 ⟨i.val + 1, by {
      simp
      have := i.isLt
      simp only [List.length] at this
      linarith
    }⟩
    exact h1
  })
  simp at this
  specialize h1 ⟨0, by simp⟩
  simp at h1
  have ha : a > 0 := by linarith
  have : a * 1 < a*(b*l.prod) := by exact (mul_lt_mul_left ha).mpr this
  linarith
}
theorem prod_lt_one : (l : List ℝ) → (hl : l.length > 0) → (h1 : ∀ i : Fin l.length, 0 ≤ l.get i ∧ l.get i < 1) → l.prod < 1
| [] => by simp
| [a] => by simp
| (a :: b :: l) => by {
  simp
  intro h1
  have := prod_lt_one (b :: l) (by simp) (by {
    intro i
    specialize h1 ⟨i.val + 1, by {
      simp
      have := i.isLt
      simp only [List.length] at this
      linarith
    }⟩
    exact h1
  })
  simp at this
  specialize h1 ⟨0, by simp⟩
  simp at h1
  cases eq_or_lt_of_le h1.left with
  | inl h0 => simp [← h0]
  | inr ha => {
    have : a * (b * l.prod) < a * 1 := by exact (mul_lt_mul_left ha).mpr this
    linarith
  }
}


theorem take_drop_sing (l : List ℝ) : ∀ (i: Fin l.length), l = (l.take i) ++ [(l.get i)] ++ (l.drop (i + 1)) := by
  intro i
  have w : l.drop i = l.get i :: l.drop (i + 1) := by {
    exact (List.get_cons_drop l i).symm
  }
  have : l.take i ++ l.drop i = l := by exact List.take_append_drop (↑i) l
  rw [w] at this
  simp only [List.append_assoc, List.singleton_append, this]

theorem agm1 (a b : ℝ) : Bet a 1 b → a + b ≥ a*b + 1 := by
  intro hB
  wlog h : a ≤ 1 ∧ 1 ≤ b generalizing a b with w
  rw [Bet] at hB
  have : b ≤ 1 ∧ 1 ≤ a := by tauto
  specialize w b a (Or.inr this).symm this
  linarith

  have : (a-1)*(b-1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith

theorem agm2 : (l : List ℝ) → l.length ≥ 2 → (∀ i, l.get i ≥ 0) → l.prod = 1→
∃ i j : Fin l.length, i ≠ j ∧ Bet (l.get i) 1 (l.get j)
| [] => by {simp;}
| [a] => by {simp;}
| [a, b] => by {
  intros h1 h2
  simp
  intro hab
  have ha : a ≥ 0 := h2 ⟨0, by linarith⟩
  have hb : b ≥ 0 := h2 ⟨1, by linarith⟩
  have crux1 := mul_le_one_imp a b ha (Eq.le hab)
  have crux2 := mul_ge_one_imp a b ha (Eq.ge hab)

  wlog h : a ≤ 1 generalizing a b with w
  {
    have : b ≤ 1 := by tauto
    rw [mul_comm] at hab
    specialize w b a h1 _ hab hb ha crux1.symm crux2.symm this
    {
      intro i
      simp at i
      match i with
      | 0 => simp; linarith
      | 1 => simp; linarith
    }
    match w with
    | ⟨i, j, hij⟩ =>
    use j; use i
    match i, j with
    | 0, 1 => simp; exact hij.right
    | 1, 0 => simp; exact hij.right
    | 0, 0 => simp at hij
    | 1, 1 => simp at hij
  }
  cases LE.le.lt_or_eq h with
  | inl hT => {
    have : ¬ a ≥ 1 := not_le.mpr hT
    have hl' : b ≥ 1 := by tauto
    use 0; use 1
    simp
    exact Or.inl ⟨h, hl'⟩
  }
  | inr hE => {
    simp only [hE, one_mul] at hab
    use 0; use 1
    simp [hE, hab, Bet]
  }
}
| a :: (b :: l') => by {
  let l'' := b :: l'
  have quirk : b :: l' = l'' := Eq.refl _
  have hl' : l''.length ≥ 1 := by simp; linarith
  rw [quirk]
  generalize l'' = l at *

  intros _ h1 h2
  simp at h2
  by_cases h : (a ≥ 1)
  { -- pos
    have : ∃ i, l.get i ≤ 1 := by {
      apply by_contradiction
      intro h'
      simp at h'
      have crux1 := prod_gt_one l (by linarith) h'
      have crux2 := mul_le_one_imp a (l.prod) (h1 ⟨0, by simp⟩) (by linarith)

      cases LE.le.eq_or_gt h with
      | inl ha1 => {
        simp [ha1] at h2
        simp [h2] at crux1
      }
      | inr ha' => {
        have : ¬ a ≤ 1 := by linarith
        have : l.prod ≤ 1 := by tauto
        linarith only [this, crux1]
      }
    }
    match this with
    | ⟨j, hj⟩ => {
      use ⟨0, by simp⟩
      use ⟨j + 1, by {
        have := j.isLt
        simp
        linarith
      }⟩
      simp
      rw [Fin.eq_mk_iff_val_eq]

      use (Nat.succ_ne_zero j).symm
      apply Or.inr
      exact ⟨hj, h⟩
    }
  }
  { -- neg
    have : ∃ i, l.get i ≥ 1 := by {
      apply by_contradiction
      intro h'
      simp at h'
      have crux1 := prod_lt_one l (by linarith) (
        fun i => ⟨
          h1 (⟨i.val + 1, by {
          have := i.isLt
          simp
          linarith
          }⟩),

          h' i
        ⟩
      )
      have crux2 := mul_ge_one_imp a (l.prod) (h1 ⟨0, by simp⟩) (by linarith)
      have : l.prod ≥ 1 := by tauto
      linarith only [this, crux1]
    }
    match this with
    | ⟨j, hj⟩ => {
      use ⟨0, by simp⟩
      use ⟨j.val + 1, by {
        have := j.isLt
        simp
        linarith
      }⟩
      simp
      rw [Fin.eq_mk_iff_val_eq]
      use (Nat.succ_ne_zero j).symm

      apply Or.inl

      exact ⟨by linarith, hj⟩
    }
  }
}

theorem agm3 : (l : List ℝ) → l.length ≥ 1 → (∀ i, l.get i ≥ 0) → l.prod = 1 →
  l.sum ≥ l.length
| [] => by simp
| [a] => by {
  simp
  intros _ ha
  linarith
}
| [a, b] => by {
  simp
  intros h hab

  have ha := h ⟨0, by simp⟩
  simp at ha
  have hb := h ⟨1, by simp⟩
  simp at hb
  have : a*b ≥ 0 := by exact mul_nonneg ha hb

  have : (a*b).sqrt = 1 := by {
    rw [hab]
    simp
  }
  rw [← this]
  have : (a.sqrt - b.sqrt)^2 ≥ 0 := by exact sq_nonneg (Real.sqrt a - Real.sqrt b)
  ring_nf at this
  rw [← Real.sqrt_mul ha, Real.sq_sqrt ha, Real.sq_sqrt hb] at this
  linarith
}
| a :: b :: c :: l' => by {
  have hl : (c :: l').length ≥ 1 := by {
    simp
    linarith
  }
  generalize (c :: l') = l at *
  intros hL h0 h1
  match agm2 (a :: b :: l) (by simp; linarith) h0 h1 with
  | ⟨⟨i_val, is⟩, ⟨j_val, js⟩, hij⟩ =>
    wlog h' : i_val < j_val generalizing i_val j_val with w'
    have crux : j_val < i_val := by
      simp at hij
      simp at h'
      exact Nat.lt_of_le_of_ne h' (id (Ne.symm hij.left))
    have := take_drop_sing (a :: b :: l) ⟨i_val, is⟩

    exact w' j_val (by assumption) (i_val) (by assumption) ⟨hij.left.symm, hij.right.symm⟩ crux

    --
    have crux1 := take_drop_sing (a :: b :: l) ⟨i_val, is⟩
    have crux2 := take_drop_sing ((a :: b :: l).drop (i_val + 1)) ⟨j_val - (i_val+1), by {
      simp
      have q : (l.length.succ.succ - (i_val+1)) + (i_val+1) = l.length.succ.succ := by {
        apply Nat.sub_add_cancel
        simp at is
        linarith
      }
      have : (j_val - (i_val + 1)) + (i_val + 1) = j_val := by
        {
        apply Nat.sub_add_cancel
        exact h'
        }
      simp at js
      rw [← q, ← this] at js
      have : j_val - (i_val + 1) < l.length.succ.succ - (i_val + 1) := by linarith only [js]
      simp at this
      exact this
    }⟩
    simp only [List.drop_succ_cons, List.drop_drop] at crux2
    generalize ((b :: l).drop i_val).get _ = B at crux2
    generalize (a :: b :: l).get ⟨i_val, is⟩ = A at crux1
    simp only [List.length_cons, List.drop_succ_cons] at crux1
    rw [crux2] at crux1
    have : (j_val - (1 + i_val)) + (1 + i_val) = j_val :=
      Nat.sub_add_cancel (by linarith)
    rw [add_comm, add_assoc, this] at crux1
    have : (a :: b :: l).prod =
    A * B * (((a :: b :: l).take i_val) ++ ((b :: l).drop i_val).take (j_val - (i_val + 1)) ++ (b::l).drop (j_val)).prod := by {
      simp only [ge_iff_le, List.append_assoc, List.prod_append]
      rw [crux1]
      ring
    }
    have crux3 : (((a :: b :: l).take i_val) ++ ((b :: l).drop i_val).take (j_val - (i_val + 1)) ++ (b::l).drop (j_val)).length ≥ 1 := by {
      have woops : (a :: b :: l).length ≥ 3 := by simp; linarith
      rw [crux1, crux2] at woops
      simp only [List.append_assoc, List.length_append, List.length_singleton] at woops
      simp only [List.length_append, List.length_singleton, List.length_cons] at woops
      simp only [List.append_assoc, List.length_append]
      linarith
      simp only [ge_iff_le, List.append_assoc, List.length_append, List.length_take, List.length_drop, tsub_le_iff_right]
      have : i_val < (a :: b :: l).length := is
      rw [min_eq_left_of_lt is]

      have : min (j_val - (i_val + 1)) (List.length (b :: l) - i_val) = j_val - (i_val + 1) := by {
        apply min_eq_left_of_lt
        simp
        simp at js
        have : j_val- (i_val + 1) < l.length.succ.succ - (i_val + 1) :=
          (tsub_lt_tsub_iff_right (by linarith)).mpr js
        simp at this
        exact this
      }
      rw [this]
      have : j_val ≥ (i_val + 1) := by exact h'
      simp
      ring_nf
      have p : (j_val - (1 + i_val):ℕ) = (j_val - (1 + i_val) : ℤ) := Int.ofNat_sub h'
      have q : (Nat.succ (List.length l) - j_val : ℕ) = (Nat.succ (List.length l) - j_val : ℤ) := Int.ofNat_sub (by {
        simp at js
        have : j_val.succ ≤ l.length.succ.succ := by exact js
        linarith
      })
      apply Int.ofNat_le.mp
      push_cast
      rw [p, q]
      ring
      simp
      exact hl
    }
    -- have : ∀ u, (((a :: b :: l).take i_val) ++ ((b :: l).drop i_val).take (j_val - (i_val + 1)) ++ (b::l).drop (j_val)).get u ≥ 0 := by {
    --   rintro ⟨u_val, us⟩
    --   cases Nat.lt_or_ge u_val i_val with
    --   | inl w => {
    --     have : (((a :: b :: l).take i_val) ++ (((b :: l).drop i_val).take (j_val - (i_val + 1)) ++ (b::l).drop (j_val))).get ⟨u_val = ((a :: b :: l).take i_val).get u_val
    --   }
    -- }
    generalize ((a :: b :: l).take i_val) ++ ((b :: l).drop i_val).take (j_val - (i_val + 1)) ++ (b::l).drop (j_val) = lC at *
    have : A*B*lC.prod = ((A*B)::lC).prod := by simp only [List.prod_cons]
    have := agm3 (A*B::lC) (by {
      simp
      linarith
      })

}
