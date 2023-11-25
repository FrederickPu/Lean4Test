--import Lean4Test.AGM

import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Tactic.Polyrith

example (P : Prop) : P ∨ ¬P := by exact em P
#check List.range
def f (x : ℕ) : ℕ := Id.run do
  let mut out : ℕ := 0
  for _ in List.range x do
    out := out + 1
  return out

#check List.ForIn.eq
theorem lem :  ∀ n : ℕ, f n = n := by
 intro n
 simp [f]
 induction n with
 | zero => rfl
 | succ n hn => {
  rw [List.range, List.range.loop]
 }


example (α β x y y' : ℝ) (h : 2*(x^2+y^2)*(2*x + 2*y*y') = (α*2*x + β*2*y*y')) :
  (2*x^2*y+2*y^3 - β*y)*y' = -(2*x^3+2*x*y^2 - α*x) := by
  linear_combination h/2

theorem kevin {a b c : ℝ} : a ≥ 0 → c > 0 → b*a = c → b > 0 := by
  intros ha hc h
  apply by_contradiction
  intro hb
  simp at hb
  have han : a ≠ 0 := by {
    intro q
    simp [q] at h
    linarith
  }
  have hbn : b ≠ 0 := by {
    intro q
    simp [q] at h
    linarith
  }
  have : a > 0 := by exact Ne.lt_of_le (id (Ne.symm han)) ha
  have : a*b < 0 := by exact Linarith.mul_neg (Ne.lt_of_le hbn hb) this
  linarith
theorem kevin1 {a b c : ℝ} : a > 0 → c ≥ 0 → b*a = c → b ≥ 0 := by
  intros ha hc h
  have : a ≠ 0 := by linarith
  apply by_contradiction
  intro hb
  simp at hb
  have : b*a < 0 := by exact mul_neg_of_neg_of_pos hb ha
  linarith

example (α β x y : ℝ) (hba : β < 2*α) (ha : α > 0) (hb : β > 0) (h : α*x^2 + β*y^2 = (x^2 + y^2)^2) : 2*x^2*y+2*y^3 - β*y = 0 ↔ (x, y) ∈ ({(0, 0), (α.sqrt, 0), (-α.sqrt, 0)} : Set (ℝ × ℝ)) := by
  apply Iff.intro
  intro h'
  have : y*(2*x^2 + 2*y^2 - β) = 0 := by linear_combination h'
  simp at this
  cases this with
  | inl l => {
    rw [l] at h
    ring_nf at h
    have : x^2*(x^2 - α) = 0 :=
      by linear_combination -h
    have w : (x - α.sqrt)*(x + α.sqrt) = x^2 -α := by
    {
      ring
      rw [Real.sq_sqrt (le_of_lt ha)]
    }
    rw [← w] at this
    simp at this
    simp

    rcases this with h1 | h2 | h3
    exact Or.inl ⟨h1, l⟩
    exact Or.inr <| Or.inl ⟨by linarith, by linarith⟩
    exact Or.inr <| Or.inr ⟨by linarith, by linarith⟩
  }
  | inr r => {
    apply False.elim

    have crux1 : x^2 + y^2 = β / 2 := by linear_combination r / 2
    rw [crux1] at h
    have e : (β - α)*x^2 = β^2 / 4 := by linear_combination β*crux1 - h
    have : β - α > 0 := kevin (sq_nonneg x) (by linarith [sq_pos_of_pos hb]) e

    have crux2 : (β - α)*y^2 = β*(β - 2*α)/4 := by linear_combination h - α*crux1
    rw [mul_comm β, mul_div_assoc (β - 2 * α) β 4] at crux2
    have := sq_nonneg y
    have : (β - α)*y^2 ≥ 0 := by exact (zero_le_mul_left (by linarith)).mpr this
    have : β - 2*α ≥ 0 := by exact kevin1 (by linarith) this (id crux2.symm)
    linarith
  }

  {
    intro hw
    simp at hw
    rcases hw with h1 | h2 | h3
    simp [h1]
    simp [h2]
    simp [h3]
  }


#check inv_mul_cancel
theorem Real.mul_left_cancel {a b c: ℝ} : c ≠ 0 →  c*a = c*b → a= b := by
  intros hc h
  have : c⁻¹ * (c*a) = c⁻¹*(c*b) := by exact congrArg (HMul.hMul c⁻¹) h
  simp only [← mul_assoc, inv_mul_cancel hc, one_mul] at this
  exact this

example (α β x y : ℝ) (ha : α > 0) (hb : β > 0) (h : α*x^2 + β*y^2 = (x^2 + y^2)^2) : 2*x^2*y+2*y^3 - β*y = 0 ↔ (x, y) ∈ ({(0, 0), (α.sqrt, 0), (-α.sqrt, 0)} : Set (ℝ × ℝ)) ∪ {p : ℝ × ℝ | (β - α)*p.fst^2 = β^2 / 4 ∧ (β - α)*p.snd^2 = β*(β - 2*α)/4} := by
  apply Iff.intro
  intro h'
  have : y*(2*x^2 + 2*y^2 - β) = 0 := by linear_combination h'
  simp at this
  cases this with
  | inl l => {
    rw [l] at h
    ring_nf at h
    have : x^2*(x^2 - α) = 0 :=
      by linear_combination -h
    have w : (x - α.sqrt)*(x + α.sqrt) = x^2 -α := by
    {
      ring
      rw [Real.sq_sqrt (le_of_lt ha)]
    }
    rw [← w] at this
    simp at this
    simp

    apply Or.inl
    rcases this with h1 | h2 | h3
    exact Or.inl ⟨h1, l⟩
    exact Or.inr <| Or.inl ⟨by linarith, by linarith⟩
    exact Or.inr <| Or.inr ⟨by linarith, by linarith⟩
  }
  | inr r => {
    simp
    apply Or.inr
    have crux : x^2 + y^2 = β / 2 := by linear_combination r / 2
    rw [crux] at h
    have e : (β - α)*x^2 = β^2 / 4 := by linear_combination β*crux - h
    exact ⟨by linear_combination β*crux - h, by linear_combination h - α*crux⟩
  }
  {
    simp
    intro w
    rcases w with (h1 | h2 | h3) | h4
    simp [h1]
    simp [h2]
    simp [h3]
    {
      have : (β - α) * (x^2 + y^2) = (β  - α) * (β / 2) := by linear_combination h4.left + h4.right
      have crux : β - α ≠ 0 := by {
        intro q
        have := h4.left
        simp [q] at this
        linarith [sq_pos_of_pos hb]
      }
      have : (x^2 + y^2) = β / 2 := Real.mul_left_cancel crux this
      linear_combination y*2*this
    }
  }

example (α β : ℝ) (ha : α > 0) (hb : β > 0)  (hba : β < 2*α) : {p : ℝ × ℝ | (β - α)*p.fst^2 = β^2 / 4 ∧ (β - α)*p.snd^2 = β*(β - 2*α)/4} = ∅ := by
{
  apply Set.ext
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Prod.forall]
  intros x y h
  have crux1 : β - α > 0 := kevin (sq_nonneg x) (by linarith [sq_pos_of_pos hb]) h.left
  have : (β - α)*y^2 ≥ 0 := by exact (zero_le_mul_left (by linarith)).mpr (sq_nonneg y)
  rw [mul_comm β, mul_div_assoc (β - 2 * α) β 4] at h
  -- have : (β - α)*x^2 = β*(β - 2*α)/4 :=
  have : β - 2*α ≥ 0 := kevin1 (by linarith) this h.right.symm
  linarith
}

#check deriv

example : deriv (fun (x:ℝ) => x^2) 1 = 2*1 :=
by simp

#check ℝ

def hello := "world"

def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

def List.noDupps {α : Type} (l : List α) :=
∀ i j : Fin (l.length), l.get i = l.get j → i = j

theorem wow : ∀ n : Nat, fib n ≤ n := by sorry

#check Nat.zero_lt_succ
#check Nat.le_of_lt_succ
#check Nat.succ_le_of_lt
#check Nat.lt_of_lt_of_le

#check Nat.not_lt_eq
theorem lt_one_imp : ∀ n : Nat, n < 1 → n = 0
| 0 => fun _ => Eq.refl 0
| n + 1 => by {
  intro h;
  have := Nat.zero_lt_succ n;
  have := Nat.succ_le_of_lt this;
  have crux := Nat.lt_of_lt_of_le h this;
  apply False.elim;
  have := Nat.not_lt_eq (n + 1) (n+1);
  have : ¬n + 1 < n + 1 := by {
    rw [this];
    exact Nat.le_of_eq (Eq.refl (n+1));
  };
  exact this crux;
}

#check Nat.add_lt_add_left
theorem List.map_comp {α β γ : Type} (f : α → β) (g : β → γ) :
∀ l : List α, l.map (g ∘ f) = (l.map f).map g
| [] => by {
  simp [List.map];
}
| List.cons a l => by {
  simp [List.map];
  exact List.map_comp f g l
}
def Fin.toFinSucc {n : Nat} : Fin n → Fin (n + 1) :=
fun ⟨x, hx⟩ => ⟨x, by {
  have := Nat.lt_succ_self n;
  exact Nat.lt_trans hx this;
}⟩

theorem Fin.toFinSucc_invar {n : Nat} (f : Nat → Nat) : f ∘ (fun (x : Fin n) => x.toFinSucc) = fun (x : Fin n) => f x:= by
{
  apply funext;
  intro x;
  simp [Fin.toFinSucc];
}

#eval ((⟨7⟩ : Fib) : Nat)
-- largest number in the list less than a.succ
-- defualt output is 0
#check List.maximum?
#check List.range
#check PSigma (fun x => x < 0)
theorem tiny : ∀ n : Nat, ∃ l : List Nat, (l.map fib).sum = n
| 0 => ⟨[0], by {
  simp;
}⟩
| n + 1 => match tiny n with
 | ⟨l, hl⟩ => ⟨List.cons 1 l, by {
  simp [List.map, List.sum]
  rw [fib, hl]
  rw [Nat.add_comm]
 } ⟩

def Nat.dvd (a b : Nat) : ∃ k : Nat, k*a = b
def combat :

#check 0 ≤ 1 ∧ 1 < 2
def Nat.isPrime (n : Nat) := ∀ k : Nat, 1 < k ∧ k ≤ n → k  n

theorem boom : ∀ n : Nat, ∃ l : List (PSigma (fun x => (fib x) < n + 2)), (l.map (fun x => fib x.fst)).sum = n ∧ l.noDupps
| 0 => ⟨[⟨0, by simp [fib]⟩], by {
  apply And.intro;
  simp [List.sum];
  intros i j h;
  apply Fin.eq_of_val_eq;
  rw [lt_one_imp i.val i.isLt]
  rw [lt_one_imp j.val j.isLt];
}⟩
| n + 1 =>
 let F := l.maximum?
 match boom (fib x) with
  | ⟨l, hl⟩ => ⟨List.cons ⟨n+1, Nat.lt_succ_self (n+1)⟩ (l.map Fin.toFinSucc), by {
    apply And.intro;
    rw [List.map, List.sum, ];
    simp;
    rw [← l.map_comp];

  }⟩
