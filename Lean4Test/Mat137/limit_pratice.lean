import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.bounds
import Mathlib.Tactic

def limit (f : ℝ → ℝ) (a L : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε
def limiti (f : ℝ → ℝ) (L : ℝ) := ∀ ε > 0, ∃ M > 0, ∀ x : ℝ, M < x → |f x - L| < ε

example : limit (fun x => x^2 + 2*x) 2 8 := by
  intros ε he
  use min (ε / 10) 1
  use (by {
    apply lt_min_iff.mpr
    exact ⟨by linarith, by linarith⟩
  })
  intros x hx
  suffices : |x^2 - 4| < ε / 2 ∧ |2*x - 4| < ε / 2
  calc
    |x ^ 2 + 2 * x - 8| = |(x^2 - 4) + (2*x - 4)| := by ring
    |(x^2 - 4) + (2*x - 4)| ≤ |x^2 - 4| + |2*x - 4| := abs_add (x^2 - 4) (2*x - 4)
    _ < ε := by linarith [this.left, this.right]
  apply And.intro
  have p : |x - 2| < (ε / 10) := by {
    calc
      |x - 2| < min (ε / 10) 1 := hx.right
      _ ≤ ε / 10 := min_le_left (ε / 10) 1
  }
  have q : |x + 2| < 5 := by {
    calc
      |x + 2| = |x - 2 + 4| := by ring
      _ ≤ |x - 2| + |4| := abs_add (x - 2) 4
      _ < min (ε / 10) 1 + |4| := by linarith [hx.right]
      _ ≤ 1 + |4| := by linarith [min_le_right (ε / 10) 1]
      _ = 5 := by norm_num [abs_of_pos]
  }
  calc
    |x^2 - 4| = |(x - 2)*(x+2)| := by simp; ring
    _ = |x - 2| * |x+2| := abs_mul (x - 2) (x+2)
    _ < (ε / 10) * 5 := mul_lt_mul'' p q (le_of_lt hx.left) (
      calc
        |x + 2|  = |(-(x+2))| := (abs_neg (x + 2)).symm
        |-(x + 2)| = |-4 - (x - 2)| := by ring
        _ ≥ |-4 - (x - 2) + (x - 2)| - |x - 2| := by linarith [abs_add (-4 - (x - 2)) (x - 2)]
        _ = 4 - |x - 2| := by ring_nf; norm_num [abs_of_pos]
        _ ≥ 4 - (min (ε / 10) 1) := by linarith [hx.right]
        _ ≥ 0 := by linarith [min_le_right (ε / 10) 1]
    )
    _ = ε / 2 := by ring
  calc
    |2*x - 4| = |2*(x - 2)| := by ring
    _ = |2| * |x - 2| := abs_mul 2 (x - 2)
    _ = 2 * |x - 2| := by norm_num [abs_of_pos]
    _ < 2* (min (ε / 10) 1) := by linarith [hx.right]
    _ ≤ 2 * (ε / 10) := by linarith [min_le_left (ε / 10) 1]
    _ < ε / 2 := by linarith

#check Real.pi_le_four
example (f g : ℝ → ℝ) (hg : ∀ x : ℝ, g x > 0): limiti (f * g) 3 → ∃ M > 0, ∀ x : ℝ, x > M → f x ≥ 2 / (Real.pi * g x) := by
  intro h
  specialize h (3 - 2 / Real.pi) (by {
    norm_num
    have : 1 / Real.pi < 1 / 3 := (one_div_lt_one_div (Real.pi_pos) (by linarith)).mpr Real.pi_gt_three
    have : 2 / Real.pi < 2 / 3 :=
      calc
        2 / Real.pi  = 2 * (1 / Real.pi) := by ring
        _ < 2 * (1 / 3) := by linarith [this]
        _ = 2 / 3 := by ring
    linarith
  })
  match h with
  | ⟨M, hM, H⟩ => {
    use M
    use hM
    intros x hx
    specialize H x hx
    have : -(3 - 2 / Real.pi) < (f * g) x - 3  ∧ (f * g) x - 3 < (3 - 2 / Real.pi) := abs_lt.mp H
    have : (f * g) x > 2 / Real.pi := by linarith [this.left]
    calc
      (f x) = (f x * g x) / (g x) := (mul_div_cancel (f x) (ne_of_gt (hg x))).symm
      (f x * g x) / (g x) ≥ (2 / Real.pi) / (g x) := le_of_lt <| (div_lt_div_right (hg x)).mpr this
      _ = 2 / (Real.pi * g x) := div_div 2 Real.pi (g x)
  }

example (f : ℝ → ℝ) (a : ℝ) (hf : f a > 0): limit f a (f a) → ∃ δ > 0, ∀ x : ℝ, |x - a| < δ → f x > 0 := by
  intro h
  specialize h (f a / 2) (by linarith)
  match h with
  | ⟨δ, hd, H⟩ => {
    use δ
    use hd
    intros x hx
    specialize H x
    cases eq_or_ne x a with
    | inl l => rw [l]; exact hf
    | inr r => {
      have : x - a ≠ 0 := by exact sub_ne_zero.mpr r
      have : |x - a| > 0 := by exact abs_pos.mpr this
      specialize H ⟨this, hx⟩
      have : - (f a / 2) < f x - f a ∧ f x - f a < f a / 2 := abs_lt.mp H
      linarith [this.left]
    }

  }
