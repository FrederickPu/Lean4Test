import Lean4Test.AGM

import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

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
