import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic
import Mathlib.Data.Rat.Basic

structure NNRat where
val : Rat
isNN : 0 ≤ val

def NNRat.floor : NNRat → Nat := fun ⟨x, _⟩ => x.floor.toNat
def NNRat.ceil : NNRat → Nat := fun ⟨x, _⟩ => x.ceil.toNat

instance : Coe Nat NNRat :=
{
  coe := fun n => ⟨n, by linarith⟩
}

def NNRat.floor' {n : Nat} (x : NNRat) : Fin (n + 1) := ⟨min x.floor n, Nat.lt_succ.mpr (Nat.min_le_right x.floor n)⟩
def NNRat.ceil' {n : Nat} (x : NNRat) : Fin (n + 1) := ⟨min x.ceil n, Nat.lt_succ.mpr (Nat.min_le_right x.ceil n)⟩

open Matrix

-- a : 0, 0
-- b : 0, 1
-- c : 1, 0
-- d : 1, 1
-- b --- d
-- |     |
-- a --- c
def bilinear (a b c d : ℝ) (x y : ℚ) : ℝ :=
  a * (x * y) + b * (x * (1 - y)) + c * ((1 - x) * y) + d * ((1 - x) * (1 - y))

def billinearImageTransform (finv : NNRat × NNRat → NNRat × NNRat) {n : ℕ}: Matrix (Fin (n+1)) (Fin (n+1)) ℝ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
fun M => of fun x y =>
  let ⟨x', y'⟩ := finv ⟨x.val, y.val⟩
  bilinear (M x'.floor' y'.floor') (M x'.floor' y'.ceil') (M x'.ceil' y'.floor') (M x'.ceil' y'.ceil')
    (x'.val - x'.floor) (y'.val - y'.floor)
