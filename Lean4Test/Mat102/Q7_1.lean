import Mathlib.Data.Real.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Init.Set

-- import Data.Set.Finite
import Mathlib.Logic.Equiv.Set

example : Reflexive (fun x y : ℝ => |x - y| ≤ 3) := by
  simp only [Reflexive]
  intro x
  norm_num
example : Symmetric (fun x y : ℝ => |x - y| ≤ 3) := by
  simp only [Symmetric]
  intros x y
  conv =>
    enter [2]
    rw [abs_sub_comm]
  assumption
  tauto

#check ring
example : ¬ Transitive (fun x y : ℝ => |x - y| ≤ 3) := by
  simp only [Transitive, not_forall]
  use 3; use 0; use -1
  use (by norm_num [abs_of_nonneg])
  use (by norm_num [abs_of_nonneg])
  norm_num [abs_of_nonneg]

example : ¬ Reflexive (fun x y : ℝ => x*y > 0) := by
  simp only [Reflexive, gt_iff_lt, mul_self_pos]
  simp only [forall_eq]
example : Symmetric (fun x y : ℝ => x*y > 0) := by
  simp only [Symmetric]
  intros x y
  rw [mul_comm]
  tauto
example : Transitive (fun x y : ℝ => x*y > 0) := by
  simp only [Transitive]
  intros x y z
  intros hx hy
  have := calc
    y^2*(x*z) = (x*y)*(y*z) := (by ring)
    (x*y)*(y*z) > 0 := mul_pos hx hy
  exact pos_of_mul_pos_right this (sq_nonneg y)

example : Reflexive (fun x y : ℝ => x^2 - y = y^2 - x) := by
  simp only [Reflexive]
  tauto
example : Symmetric (fun x y : ℝ => x^2 - y = y^2 - x) := by
  simp only [Symmetric]
  intros x y h
  exact h.symm
example : Transitive (fun x y : ℝ => x^2 - y = y^2 - x) := by
  simp only [Transitive]
  intros x y z
  intros h1 h2
  linear_combination h1 + h2

example : Reflexive (fun x y : ℝ => (x - y)*(x^2 + y^2 - 1) = 0) := by
  simp only [Reflexive]
  norm_num
example : Symmetric (fun x y : ℝ => (x - y)*(x^2 + y^2 - 1) = 0) := by
  simp only [Symmetric]
  intros x y h
  linear_combination -h
example : ¬ Transitive (fun x y : ℝ => (x - y)*(x^2 + y^2 - 1) = 0) := by
  simp only [Transitive, not_forall]
  use (1 / 2)
  use ((3:ℝ).sqrt / 2)
  use (-1 / 2)

  use (by norm_num)
  use (by norm_num)
  norm_num

example : Reflexive (fun x y : ℝ => |x + y| = |x| + |y|) := by
  simp only [Reflexive]
  intro x
  ring_nf
  norm_num [abs_mul]
example : Symmetric (fun x y : ℝ => |x + y| = |x| + |y|) := by
  simp only [Symmetric]
  intros x y h
  rw [add_comm]
  linear_combination h
example : ¬ Transitive (fun x y : ℝ => |x + y| = |x| + |y|) := by
  simp only [Transitive, not_forall]
  use 3
  use 0
  use -1
  use (by norm_num)
  use (by norm_num)
  norm_num [abs_of_nonneg]

example : Reflexive (fun a b => a ∣ 2*b ∨ b ∣ 2*a) := by
  simp [Reflexive]
example : Symmetric (fun a b => a ∣ 2*b ∨ b ∣ 2*a) := by
  simp only [Symmetric]
  intros x y h
  exact Or.symm h
example : ¬ Transitive (fun a b => a ∣ 2*b ∨ b ∣ 2*a) := by
  simp only [Transitive, not_forall]
  use 15
  use 3
  use 21
  use (by norm_num)
  use (by norm_num)
  norm_num

example : Reflexive (fun x y => x + 1 / y = y + 1 / x) := by
  simp only [Reflexive]
  tauto
example : Symmetric (fun x y => x + 1 / y = y + 1 / x) := by
  simp only [Symmetric]
  intros x y
  intro h
  exact h.symm
example : Transitive (fun x y : ℝ => x + 1 / y = y + 1 / x) := by
  simp only [Transitive]
  intros x y z
  intros h1 h2
  linear_combination h1 + h2

def Function.Constant (α β : Type*) (f : α → β) := ∃ C : β, ∀ x : α, f x = C
example : Reflexive (fun (f g : ℝ → ℝ) => (f - g).Constant) := by
  simp only [Reflexive]
  intro f
  simp [Function.Constant]
example : Symmetric (fun (f g : ℝ → ℝ) => (f - g).Constant) := by
  simp only [Symmetric]
  intros f g
  intro ⟨C, hC⟩
  use -C
  intro x
  specialize hC x
  rw [← hC]
  simp
example : Transitive (fun (f g : ℝ → ℝ) => (f - g).Constant) := by
  simp only [Transitive]
  intros f g h
  rintro ⟨C1, hC1⟩
  rintro ⟨C2, hC2⟩
  use C1 + C2
  intro x
  linear_combination (norm := ring_nf) (hC1 x) + (hC2 x)
  simp only [Pi.sub_apply]
  ring


#check {y.sqrt | y : ℝ}
#check {y : ℝ | ∃ x : ℤ, y^2 = x}
example :  {y : ℝ | ∃ x : ℤ, y^2 = x} ∩ (Set.Icc 5 6) = {y : ℝ  | y ≥ 0 ∧ ∃ x : ℤ, x = y^2 ∧ y^2 ∈ Set.Icc 25 36} := by {
  ext y
  simp
  apply Iff.intro
  intro h
  match h with
  | ⟨⟨x, h⟩, h1, h2⟩ => {
    use (by linarith)
    apply And.intro
    use x
    exact h.symm
    have : 5 ≥ 0 := by linarith
    have w : 5^2 ≤ y^2 := sq_le_sq' (by linarith) h1
    have w1 : y^2 ≤ 6^2 := sq_le_sq' (by linarith) h2
    apply And.intro
    linarith
    linarith
  }
  intro h
  match h with
  | ⟨h', ⟨x, h⟩, h1, h2⟩ => {
    apply And.intro
    use x
    exact h.symm
    apply And.intro
    have : |5| ≤ |y| := by exact sq_le_sq.mp (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at this
    exact this

    have : |y| ≤ |6| := by exact sq_le_sq.mp (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at this
    exact this
  }
}

#check Set.BijOn.equiv
noncomputable example : {x : ℤ | x ∈ Set.Icc 25 36} ≃ {y : ℝ  | y ≥ 0 ∧ ∃ x : ℤ, x = y^2 ∧ y^2 ∈ Set.Icc 25 36} := by
{
  apply Set.BijOn.equiv (fun (x:ℤ) => (x:ℝ).sqrt)
  apply And.intro
  simp [Set.MapsTo]
  intros x h1 h2
  apply And.intro
  exact Real.sqrt_nonneg ↑x
  rw [Real.sq_sqrt (by norm_num; linarith)]
  apply And.intro
  use x
  apply And.intro
  exact Int.cast_le.mpr h1
  exact Int.cast_le.mpr h2

  apply And.intro
  simp [Set.InjOn]
  intros x1 h1 h1' x2 h2 h2'
  intro h
  have w : 0 ≤ x1 := by linarith
  have w1 : 0 ≤ x2 := by linarith
  have := (Real.sqrt_inj (by {
    have : ((0:ℤ) : ℝ) ≤ (x1 : ℝ) := Int.cast_le.mpr w
    push_cast at this
    exact this
  }) (by {
    have : ((0:ℤ) : ℝ) ≤ (x2 : ℝ) := Int.cast_le.mpr w1
    push_cast at this
    exact this
  })).mp h
  apply Int.cast_inj.mp this

  intro y
  intro hy
  simp at hy
  match hy with
  | ⟨h', ⟨x, h⟩, h1, h2⟩ => {
    use x
    simp
    rw [← h] at h1
    rw [← h] at h2
    apply And.intro
    exact ⟨Int.cast_le.mp h1, Int.cast_le.mp h2⟩
    rw [h, Real.sqrt_sq h']
  }
}

example : (Finset.Icc 25 36).card = 36 - 25 + 1 := by
rfl

#check List.swap
#check Set.Finite
#check Set.Finite_inter_of_left
def myGCD (a b : ℕ) := Finset.min {x : ℕ | x < a ∧ x ∣ a ∧ a ∣ b}

#check Set.powerset
example (α : Type*) (A : Set α) (f : α → Set α) : ¬ Set.SurjOn f A A.powerset := by
  simp only [Set.SurjOn]
  intro h
  specialize h <| Set.inter_subset_left A {a | a ∉ f a}
  simp at h
  match h with
  | ⟨x, hx⟩ => {
    have := Set.ext_iff.mp hx.2
    specialize this x
    simp at this
    tauto
  }

example (a b : ℝ) : a + b = 0 := by
  linarith
