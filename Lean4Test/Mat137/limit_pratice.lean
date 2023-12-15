import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.bounds
import Mathlib.Tactic

def limit (f : ℝ → ℝ) (a L : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε
def limiti (f : ℝ → ℝ) (L : ℝ) := ∀ ε > 0, ∃ M > 0, ∀ x : ℝ, M < x → |f x - L| < ε
def continuous_at (f : ℝ → ℝ) (a : ℝ) := limit f a (f a)

-- Section 1: definition of limit and continuity
-- 1 a)
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

-- 1 b)
example : limit (fun x => x / (x + 3)) 3 (1 / 2) := by
  intros ε he
  use min ε 1
  use (by {
    apply lt_min_iff.mpr
    exact ⟨by linarith, by linarith⟩
  })
  intro x ⟨hx1, hx2⟩
  have crux1 : |x - 3| < ε :=
    calc
      |x - 3| < min ε 1 := hx2
      _ ≤ ε := min_le_left ε 1
  have crux2 : |x - 3| < 1 :=
    calc
      |x - 3| < min ε 1 := hx2
      _ ≤ 1 := min_le_right ε 1
  have crux3 : 5 < x + 3 ∧ x + 3 < 7:= by
    {
      have : -1 < x - 3 ∧ x - 3 < 1 := by exact abs_lt.mp crux2
      apply And.intro
      linarith [this.left]
      linarith [this.right]
    }
  have w1 := crux3.right
  have w2 : 0 < x + 3 := by linarith [crux3.left]
  have : |x - 3| / (x + 3) < ε / 5 := div_lt_div crux1 (by linarith) (by linarith) (by linarith)
  calc
    |(fun x => x / (x + 3)) x - 1 / 2| = |(x - 3) / (x + 3)| := by ring
    _ = |x - 3| / |x + 3| := abs_div (x - 3) (x + 3)
    _ = |x - 3| / (x + 3) := by rw [abs_of_pos w2]
    _ < ε / 5 := this
    _ < ε := by linarith
#check div_lt_div

-- 1 c)
example : continuous_at (fun x => 1 / (x - 1)) 2 := by
  intros ε he
  use min (1/2) (ε/2)
  use (by {
    apply lt_min_iff.mpr
    exact ⟨by linarith, by linarith⟩
  })
  intro x ⟨hx1, hx2⟩
  have crux1 : |x - 2| < 1 / 2 := by
    calc
      |x - 2| < min (1/2) (ε/2) := hx2
      min (1/2) (ε/2) ≤ 1/2 := min_le_left (1/2) (ε/2)
  have crux2 : |x - 2| < ε / 2 := by
    calc
      |x - 2| < min (1/2) (ε / 2) := hx2
      min (1/2) (ε/2) ≤ ε / 2 := min_le_right (1/2) (ε/2)

  have : (fun x => 1 / (x - 1)) x - (fun x => 1 / (x - 1)) 2 = -(x - 2)/(x - 1) := by
  {
    ring
    have := abs_lt.mp crux1
    have : -1 + x ≠ 0 := by linarith [this.right]
    field_simp
    ring
  }
  rw [this]
  rw [abs_div, abs_neg]

  have := abs_lt.mp crux1
  have : 1/2 < x - 1 := by {
    linarith [this.left]
  }
  have w : 0 < x - 1 := by linarith
  have : |x - 2| / (x - 1) < (ε/2) / (1/2) := div_lt_div crux2 (by linarith) (by linarith) (by linarith)
  calc
    |x - 2| / |x - 1| = |x - 2| / (x - 1) := by rw [abs_of_pos w]
    |x - 2| / (x - 1) < (ε / 2) / (1 / 2) := this
    (ε / 2) / (1 / 2) = ε := by ring

-- 1 d)
example : limit (fun x => 2*x^2 + 1) (-1) 3 := by
  intros ε he
  use min (ε / 6) 1
  use (by {
    apply lt_min_iff.mpr
    exact ⟨by linarith, by linarith⟩
  })
  intro x
  intro ⟨hx1, hx2⟩
  suffices : |x^2 - 1| < ε / 2
  have : |(fun x => 2 * x ^ 2 + 1) x - 3| < ε :=
    calc
      |(fun x => 2 * x ^ 2 + 1) x - 3| = |2*(x^2 - 1)| := by simp; ring
      |2*(x^2 - 1)| = |2| * |x^2 - 1| := abs_mul 2 (x^2 - 1)
      _ = 2 * |x^2 - 1| := by norm_num [abs_of_pos]
      _ < ε := by linarith
  simp at this
  simp
  exact this

  have crux1 : |x + 1| < ε / 6 :=
    calc
      |x + 1| = |x - - 1| := by ring
      _ < min (ε / 6) 1 := hx2
      _ ≤ ε / 6 := min_le_left (ε / 6) 1
  have crux2 : |x - 1| < 3 :=
    calc
      |x - 1| = |(x - - 1) + (-2)| := by ring
      |(x - - 1) + (-2)| ≤ |x - - 1| + |-2| := abs_add (x - -1) (-2)
      |x - - 1| + |-2| = |x - -1| + 2 := by norm_num [abs_of_neg]
      _ < min (ε / 6) 1 + 2 := by linarith [hx2]
      _ ≤ 1 + 2 := by linarith [min_le_right (ε / 6) 1]
      _ = 3 := by ring
  calc
    |x^2 - 1| = |(x - 1)*(x + 1)| := by simp; ring
    _ = |x - 1| * |x + 1| := abs_mul (x - 1) (x + 1)
    _ < 3 * (ε / 6) := mul_lt_mul''  crux2 crux1 (abs_nonneg (x - 1)) (abs_nonneg (x + 1))
    _ = ε / 2 := by ring

-- 1 e)
example : limit (fun x => (x + 1) / x) 4 (5/4) := by
  intro ε he
  use min (ε / 5) 1
  use (by {
    apply lt_min_iff.mpr
    apply And.intro
    linarith
    linarith
  })
  intro x ⟨hx1, hx2⟩
  have crux1 : |x - 4| < 1 :=
    calc
      |x - 4| < min (ε / 5) 1 := hx2
      _ ≤ 1 := min_le_right (ε / 5) 1
  have crux2 : |x - 4| < ε / 5 :=
    calc
      |x - 4| < min (ε / 5) 1 := hx2
      _ ≤ ε / 5 := min_le_left (ε / 5) 1
  have : 3 < x := by linarith [(abs_lt.mp crux1).left]
  have w : 0 < 4*x := by linarith
  have : |x - 4| / x < (ε/5) / 3 := div_lt_div crux2 (by linarith) (by linarith) (by linarith)
  calc
    |(fun x => (x + 1) / x) x - 5 / 4| = |-(x - 4)/(4*x)| := by {
      apply congrArg abs
      have : x ≠ 0 := by linarith
      field_simp
      ring
    }
    |-(x - 4)/(4*x)| = |-(x - 4)| / |4*x| := abs_div (-(x - 4)) (4*x)
    _ = |x - 4| / (4*x) := by rw [abs_neg, abs_of_pos w]
    _ = (|x - 4| / x) / 4 := by {
      have : 4 ≠ 0 := by linarith
      field_simp
      left
      ring
    }
    _ < (ε / 5) / 3 / 4 := by linarith [this]
    _ ≤ ε := by linarith

-- 1 f)
example : continuous_at (fun x => x / (x + 1)) 2 := by
  intro ε he
  use min ε 1
  use (by {
    apply lt_min_iff.mpr
    apply And.intro
    exact he
    linarith
  })
  intro x ⟨hx1, hx2⟩
  have crux1 : |x - 2| < ε := by linarith [min_le_left ε 1]
  have crux2 : |x - 2| < 1 := by linarith [min_le_right ε 1]
  have := abs_lt.mp crux2
  suffices : |(x - 2)/ (x + 1)| < ε
  calc
    |(fun x => x / (x + 1)) x - (fun x => x / (x + 1)) 2| = |x / (x + 1) - 2 / 3| := by simp
    _ = |(x - 2)/(3*(x+1))| := by {
      apply congrArg
      have : (x + 1) ≠ 0 := by linarith [this]
      field_simp
      ring
    }
    _ = |x - 2| / (|3| * |(x+1)|) := by rw [abs_div, abs_mul]
    _ = (|x - 2| / |x + 1|) / |3| := by ring
    _ = (|x - 2| / |x + 1|) / 3 := by norm_num [abs_of_pos]
    _ = |(x - 2) / (x+1)| / 3 := by rw [abs_div]
    _ < ε  / 3 := by linarith [this]
    _ ≤ ε :=  by linarith
  rw [abs_div]
  have : x + 1 > 0 := by linarith [this]
  rw [abs_of_pos this]
  have : x + 1 > 1 := by linarith
  have := div_lt_div crux1 (le_of_lt this) (by linarith) (by linarith)
  linarith

#check mul_lt_mul''
#check div_lt_div
-- 2
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

-- 3
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
