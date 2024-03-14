import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Order.LocallyFinite


def Finset.comb {α : Type}  (s : Finset α) (k : ℕ) : Finset (Finset α) := s.powerset.filter (fun x => x.card = k)
#check Finset.sum_partition
#check Finset.comb
open BigOperators

def Finset.range' (a b : ℕ) : Finset ℕ := Finset.range b |>.filter (fun x => a ≤ x)

example {α : Type} (n : ℕ) (k : ℕ) (h : k < n):
  ∑ i in (Finset.range n).comb (k+1), 1 = (∑ j in Finset.range' k n, ∑ i in (Finset.range k).comb i, 1) := by {
    have := Finset.sum_partition
  }

#eval (∑ i in ({1, 2, 3} : Finset ℕ), i)
