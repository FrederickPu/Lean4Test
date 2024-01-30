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

#check ∑ x = 1 ^ 10, 2 * x
#check ∑ (x = 1) ^ 10, 2 * x

-- upper sum
noncomputable def UpperSum {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) : ℝ :=
  ∑ (i = 1) ^ P.n, sSupOver (Set.Icc (P.ι (i - 1)) (P.ι i)) f

-- lower sum
noncomputable def LowerSum {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) : ℝ :=
  ∑ (i = 1) ^ P.n, sInfOver (Set.Icc (P.ι (i - 1)) (P.ι i)) f

#check Set.univ
noncomputable def UpperIntegral (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup ((fun P => UpperSum P f) '' (Set.univ : Set (Partition a b)))

noncomputable def LowerIntegral (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf ((fun P => LowerSum P f) '' (Set.univ : Set (Partition a b)))
