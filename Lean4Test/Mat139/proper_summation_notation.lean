import Mathlib.Data.Real.Basic

-- to show suprenums and infinums exists (could use a weaker import)
import Mathlib.Analysis.Calculus.MeanValue

#check sSup
#check sInf

noncomputable def sSupOver (I : Set ℝ)  (f : ℝ → ℝ) := sSup (f '' I)
noncomputable def sInfOver (I : Set ℝ)  (f : ℝ → ℝ) := sInf (f '' I)

-- x_0, x_1, ..., x_n
def isPartition {n : ℕ} (ι : Fin (n + 1) → ℝ) (a b : ℝ) : Prop :=
  ι 0 = a ∧ ι n = b ∧ ∀ i : Fin n, ι i < ι (i + 1)

#check Nat
structure Partition  (a b : ℝ) where
  {n : ℕ}
  (ι : Fin (n + 1) → ℝ)
  (h₁ : ι 0 = a)
  (h₂ : ι n = b)
  (h : ∀ i : Fin n, ι i < ι (i + 1))

def Sum_from_to (n1 : ℕ) (n2 : ℕ) (f : ℕ → ℝ) : ℝ := List.sum ((List.range' n1 (n2-n1 + 1) 1).map f)

open Std.ExtendedBinder


-- `\sum_{i = n}^m p` in latex becomes `∑ i = n ^ m p`
syntax (name := bigsum') "∑ " extBinder " = " term:90 " ^ " term:69 ", " term:67 : term
macro_rules (kind := bigsum')
  | `(∑ $x:ident = $n ^ $m, $p) => `(Sum_from_to $n $m (fun $x:ident ↦ $p))

-- `\sum_{i = n}^m p` in latex becomes `∑ (i = n) ^ m p`
syntax (name := bigsum'_verbose) "∑ " "(" extBinder " = " term:90 ")" " ^ " term:69 ", " term:67 : term
macro_rules (kind := bigsum'_verbose)
  | `(∑ ($x:ident = $n) ^ $m, $p) => `(Sum_from_to $n $m (fun $x:ident ↦ $p))


example (a b : ℝ) (f : ℝ → ℝ) : a = b → f a = f b := by exact fun a_1 => congrArg f a_1
theorem sumOver_eq (n1 : ℕ) (n2 : ℕ) (hn : n1 ≤ n2) (f g : ℕ → ℝ) : (∀ i ∈ (Set.Icc n1 n2), f i = g i) →
  ∑ (i = n1) ^ n2, f i = ∑ (i = n1) ^ n2, g i := by
  intro h
  rw [Sum_from_to]
  apply congrArg
  have : ∀ i : ℕ, i ∈ Set.Icc n1 n2 ↔ i ∈ List.range' (n1) (n2 - n1 + 1) := by {
    intro i
    apply Iff.intro
    simp
    intros h1 h2
    apply And.intro
    linarith
    {
      have : n1 ≤ n2 := by linarith
      rw [← add_assoc]
      rw [Nat.add_sub_of_le this]
      exact Nat.lt_succ.mpr h2
    }

    simp
    ring
    intros h1 h2
    apply And.intro
    exact h1
    rw [add_assoc] at h2
    rw [Nat.add_sub_of_le hn] at h2
    linarith
  }
  generalize List.range' n1 (n2 - n1 + 1) = l at this
  have : ∀ i ∈ l, f i = g i := by {
    intro i hi
    have := (this i).mpr hi
    exact h i this
  }
  exact List.map_congr this

#check ∑ x = 1 ^ 10, 2 * x
#check ∑ (x = 1) ^ 10, 2 * x

noncomputable def UpperSum {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) : ℝ :=
  ∑ (i = 1) ^ P.n, (sSupOver (Set.Icc (P.ι (i - 1)) (P.ι i)) f) * (P.ι i - P.ι (i - 1))
noncomputable def LowerSum {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) : ℝ :=
  ∑ (i = 1) ^ P.n, (sInfOver (Set.Icc (P.ι (i - 1)) (P.ι i)) f) * (P.ι i - P.ι (i - 1))

#check Set.univ
-- L_P ≤ \underline{I} ≤ \overline{I} ≤ U_P
noncomputable def UpperIntegral (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf ((fun P => UpperSum P f) '' (Set.univ : Set (Partition a b)))
noncomputable def LowerIntegral (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup ((fun P => LowerSum P f) '' (Set.univ : Set (Partition a b)))


section mat139A1

-- #check Real.le_sSup_iff
-- #check Real.sInf_le_iff

-- #check le_sSup
-- #check sInf_le

#check isGLB_iff_le_iff
#check isLUB_iff_le_iff

#check isGLB_sInf
#check isLUB_sSup

#check (![1, 2, 3] : Fin 3 → Nat)

#check List.sum_const_nat
#check List.sum_eq

#check ((2 : ℕ) : Fin 3)

example (a b c : ℕ) (h : a < b) (h1 : b = c) : a < c := by exact Nat.lt_of_lt_of_eq h h1
theorem Partition.crux {a b : ℝ} (P : Partition a b) : ∀ i ∈ Set.Icc 0 P.n, ∀ j ∈ Set.Icc 0 P.n, i < j → P.ι i < P.ι j
| i, hi, j, hj => by {
  intro h
  have := P.h ⟨i, by linarith [hj.right]⟩
  simp only at this
  have : j - i ≥ 1 := le_tsub_of_add_le_left h
  have : j ≥ i := Nat.le_of_lt h
  have : (j - i) + i = j := Nat.sub_add_cancel this
  rw [← this, Nat.add_comm _ i]
  simp only [ge_iff_le, Nat.cast_add]

  match h : (j - i) with
  | 0 => linarith
  | 1 => exact P.h ⟨i, by linarith [hj.left, hj.right]⟩
  | Nat.succ (Nat.succ n) => {

    rw [h, Nat.succ_add] at this
    have w := crux P i (⟨by linarith [hj.left, hj.right], by linarith [hj.left, hj.right]⟩) (n + 1 +  i)
    specialize w (⟨by linarith [hj.left, hj.right], by linarith [hj.left, hj.right]⟩) (by {
       linarith [hj.left, hj.right]
    })
    have := P.h ⟨Nat.succ n + i, by {
      linarith [hj.left, hj.right]
    }⟩
    push_cast at this
    push_cast at w
    ring_nf at this
    ring_nf at w

    push_cast
    ring_nf
    rw [add_assoc, add_comm (i : Fin (P.n + 1)) (n : Fin (P.n + 1))]
    rw [← add_assoc]
    linarith
  }
}
termination_by crux i hi j hj => j - i
decreasing_by {
  simp_wf
  simp at *
  linarith
}

example (P : Partition 0 2) (f : ℝ → ℝ) (C : ℝ) (hf : ∀ x ∈ Set.Icc 0 2, f x = C) : UpperSum P f = C * 2 := by
  rw [UpperSum]
  suffices :  C * 2 = ∑ (i = 1) ^ P.n, sSupOver (Set.Icc (P.ι (i - 1)) (P.ι i)) f
  rw [this]
  apply sumOver_eq
  have w1 := P.h₁
  have w2 := P.h₂
  cases em (1 ≤ P.n) with
    | inl l => exact l
    | inr h =>
      simp at h
      have : (P.n : Fin (P.n + 1)) = 0 := by {
        rw [h]
        simp
      }
      have :  Partition.ι P 0 = Partition.ι P ↑P.n := congrArg P.ι (id this.symm)
      linarith

  intro i hi
  have : f '' (Set.Icc (P.ι (i - 1)) (P.ι i)) = {C} := by {
    ext x
    simp only [Set.mem_image, Set.mem_singleton_iff]
    apply Iff.intro
    intro ⟨y, hy⟩
    have : P.ι i ≤ 2 := by {
      cases em (i = P.n) with
      | inl l => rw [l, P.h₂]
      | inr r =>
        have : i < P.n := by exact Nat.lt_of_le_of_ne hi.right r
        have := P.crux i (⟨by linarith [hi.left], by linarith [hi.right]⟩) P.n (⟨by linarith [hi.left], by linarith [hi.right]⟩) (by {
          have : 1 + (i - 1) = i := by exact Nat.add_sub_of_le hi.left
          linarith [hi.right]
        })

        rw [P.h₂] at this
        linarith
    }

  }

example (f : ℝ → ℝ) (C : ℝ) (h : ∀ x ∈ Set.Icc 0 2, f x = C): UpperIntegral 0 2 f = 2 * C := by
{
  have := Real.is_glb_sInf ((fun P => UpperSum P f) '' (Set.univ : Set (Partition 0 2))) (sorry) (sorry)
  rw [isGLB_iff_le_iff] at this
  specialize this (2*C)
}

example (f : ℝ → ℝ) (C : ℝ) (h : ∀ x ∈ Set.Icc 0 2, f x = C) [CompleteSemilatticeInf ℝ]: UpperIntegral 0 2 f = 2 * C := by
{
  have woop : f '' Set.Icc 0 2 = {C} := by {
      ext x
      simp only [Set.mem_image, Set.mem_singleton_iff]
      apply Iff.intro
      intro ⟨y, hy, H⟩
      rw [← H]
      exact h y hy
      intro hx
      use 0
      use (⟨by linarith, by linarith⟩)
      rw [hx]
      exact h 0 (⟨by linarith, by linarith⟩)
    }
  have : UpperIntegral 0 2 f ≤ 2*C := by
    let P : Partition 0 2 := ⟨![0, 2], rfl, rfl, by {
      intro i
      simp only [Fin.coe_fin_one, Nat.cast_zero, Matrix.cons_val_zero, zero_add,
        Matrix.cons_val_one, Matrix.head_cons, zero_lt_two]
    }⟩
    rw [UpperIntegral]
    rw [Real.sInf_le_iff]
    intros ε he
    use 2*C
    simp
    apply And.intro
    use P
    simp [UpperSum, Sum_from_to, sSupOver]
    rw [woop]
    simp
    linarith
    exact he
    simp
    rw [BddBelow, Set.Nonempty]
    use C
    simp [lowerBounds]
    intro P
    rw [UpperSum]
    sorry

    use 2*C
    simp
    use P
    simp [UpperSum, Sum_from_to, sSupOver]
    rw [woop, csSup_singleton]
    linarith
}
end mat139A1
