import Mathlib.Data.Real.Basic
import Mathlib.Tactic

#check ℝ
#check Real.sqrt_le_sqrt
theorem AGM1 (x y : ℝ) : x*y ≤ ((x + y) / 2)^2 := by
  have : (x - y)^2 ≥ 0 := sq_nonneg _
  linarith
theorem AGM2 (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : (x*y).sqrt ≤ (x + y) / 2 := by
  have := AGM1 x y
  -- have : x*y ≥ 0 := by exact mul_nonneg hx hy
  have : (x*y).sqrt ≤ (((x + y) / 2)^2).sqrt := Real.sqrt_le_sqrt this
  rw [Real.sqrt_sq (by linarith)] at this
  exact this

example (s t : ℝ) : s*t ≤ ((4*s + 9*t) / 12)^2 := calc
  _ = ((4 * s + 9 * t) / 2)^2 / 36 := by ring
  _ ≥ (4*s)*(9*t) / 36 := by linarith [AGM1 (4*s) (9*t)]
  _ = s*t := by ring
example (m : ℝ) (hm : m > 0) : m + 4 / m ≥ 4 := calc
  m + 4 / m ≥ 2 * (m * (4 / m)).sqrt := by {
    have := AGM2 m (4 / m) (by linarith) (le_of_lt <| div_pos (by linarith) hm)
    linarith
  }
  2 * (m * (4 / m)).sqrt = 2 * (4 : ℝ).sqrt := by {
    have : m ≠ 0 := ne_of_gt hm
    have : m * (4 / m) = 4 := mul_div_cancel' 4 this
    rw [this]
  }
  2 * (4 : ℝ).sqrt = 4 := by {
    have : (4 : ℝ).sqrt = 2 := by {
      have : (4:ℝ) = (2:ℝ)^2 := by norm_num
      rw [this]
      rw [Real.sqrt_sq]
      linarith
    }
    rw [this]
    norm_num
  }

example (A B : Set ℝ) : (A \ B) \ C = A \ (B ∪ C) := by
  ext x
  simp
  tauto
example (A B : Set ℝ) : (A \ B) ∩ (B ∩ A) = ∅ := by
  ext x
  simp
  tauto
example (A B : Set ℝ) : (A \ B) ⊆ (B \ A) → A ⊆ B := by
  intro h
  intro x
  intro hx
  apply by_contradiction
  intro hb
  have : x ∈ A \ B := Set.mem_diff_of_mem hx hb
  have : x ∈ B := by exact Set.mem_of_mem_diff (h this)
example (A B C : Set ℝ) : A ⊆ B → B ⊆ C → (C \ A) ⊆ B → C = A ∪ B := by
  intros h1 h2 h3
  ext x
  apply Iff.intro
  intro hc
  apply by_contradiction
  intro h
  simp [not_or] at h
  have : x ∈ C \ A := Set.mem_diff_of_mem hc h.left
  have := h3 this
  exact h.right this

  intro hc
  simp at hc
  cases hc with
  | inl l => exact h2 (h1 l)
  | inr r => exact h2 r

#check Monotone
#check Function.Surjective
#check Set.SurjOn
#check Set.MapsTo
example (f : ℝ → ℝ) : Set.MapsTo f (Set.Ioi 0) (Set.Ici 0) → Set.SurjOn f (Set.Ioi 0) (Set.Ici 0) → ¬ StrictMonoOn f (Set.Ioi 0) := by
  intros h h'
  have h0 : 0 ∈ Set.Ici (0:ℝ) := by simp
  have crux1 := h' h0
  simp at crux1
  match crux1 with
  | ⟨x, hx⟩ => {
    have w : x / 2 ∈ Set.Ioi 0 := by {
      simp
      exact half_pos hx.left
    }
    have := h w
    simp at this
    intro H
    have := H w hx.left (by linarith)
    linarith
  }
example (f : ℝ → ℝ) : Set.MapsTo f (Set.Ioi 0) (Set.Ici 0) → Set.SurjOn f (Set.Ioi 0) (Set.Ici 0) → ¬ StrictAntiOn f (Set.Ioi 0) := by
  intros h h'
  have h0 : 0 ∈ Set.Ici (0:ℝ) := by simp
  have crux1 := h' h0
  simp at crux1
  match crux1 with
  | ⟨x, hx⟩ => {
    have w1 : x + 1 ∈ Set.Ioi 0 := by {
      simp
      linarith
    }
    have c1 :=  h w1
    intro H
    specialize H hx.left w1 (by linarith)
    simp at c1
    linarith
  }

theorem luigi1 : Set.BijOn (fun x => x + 2) (Set.Iic (-2:ℝ)) (Set.Iic 0) := by
  apply And.intro
  intros x hx
  simp
  simp at hx
  linarith
  apply And.intro
  intros x hx y hy H
  simp at H
  exact H

  intros y hy
  simp
  simp at hy
  exact hy
theorem luigi2 : Set.BijOn (fun x => x - 102) (Set.Ioi (102:ℝ)) (Set.Ioi 0) := by
  apply And.intro
  intros x
  simp
  apply And.intro
  intros x hy y hy
  simp

  intros y hy
  simp
  exact hy

#check ((Set.Iic (-2:ℝ)) ∪ (Set.Ioi (102:ℝ)))
#check @Set.univ ℝ
#check ite
#check Set.BijOn.of_equiv_symm
#check Set.BijOn.of_equiv
#check Set.equiv_union_of_equiv
#check DecidablePred
#check Set.ext_iff
#check Set.BijOn
theorem womp {A B C D : Set ℝ} [DecidablePred A] {f g : ℝ → ℝ} : Set.BijOn f A B → Set.BijOn g C D → A ∩ C = ∅ → B ∩ D = ∅ → (A ∪ C : Set ℝ) ≃ (B ∪ D : Set ℝ) := by
  intros hf hg AC BD
  apply Set.BijOn.equiv (fun x => ite (A x) (f x) (g x))
  apply And.intro
  intro x
  intro hx
  cases hx with
  | inl l => {
    have : A x := by exact l
    simp [this]
    left
    exact hf.1 l
  }
  | inr r => {
    have := Set.ext_iff.mp AC x
    simp at this
    have : ¬ (A x) := by tauto
    simp [this]
    right
    exact hg.1 r
  }

  apply And.intro
  intros x hx y hy
  cases hx with
  | inl lx => {
    have : A x := lx
    simp only [if_pos this]
    cases hy with
    | inl ly => {
      have : A y := ly
      simp only [if_pos this]
      intro H
      exact hf.2.1 lx ly H
    }
    | inr ry => {
      have := Set.ext_iff.mp AC y
      simp at this
      have : ¬ (A y) := by tauto
      simp only [if_neg this]
      intro H
      have := hf.1 lx
      have := hg.1 ry
      rw [← H] at this
      have := Set.ext_iff.mp BD (f x)
      simp at this
      tauto
    }
  }
  | inr rx => {
    have := Set.ext_iff.mp AC x
    simp at this
    have : ¬ (A x) := by tauto
    simp only [if_neg this]
    cases hy with
    | inl ly => {
      have : A y := ly
      simp only [if_pos this]
      intro H
      have := hf.1 ly
      have := hg.1 rx
      rw [H] at this
      have := Set.ext_iff.mp BD (f y)
      simp at this
      tauto
    }
    | inr ry => {
      have := Set.ext_iff.mp AC y
      simp at this
      have : ¬ (A y) := by tauto
      simp only [if_neg this]
      exact hg.2.1 rx ry
    }
  }

  {
    intros y hy
    simp
    cases hy with
    | inl l => {
      match hf.2.2 l with
      | ⟨x, hx, Hx⟩ => {
        use x
        use (Or.inl hx)
        have : A x := hx
        simp only [if_pos this]
        exact Hx
      }
    }
    | inr r => {
      match hg.2.2 r with
      | ⟨x, hx, Hx⟩ => {
        use x
        have := Set.ext_iff.mp AC x
        simp at this
        have : ¬ (A x) := by tauto
        simp only [if_neg this]
        use (Or.inr hx)
      }
    }
  }
#check Equiv
#check Quot

noncomputable example : ((Set.Iic (-2:ℝ)) ∪ (Set.Ioi (102:ℝ)) : Set ℝ) ≃ (Set.Iic 0 ∪ Set.Ioi 0 : Set ℝ) := by
  have : DecidablePred (Set.Iic (-2:ℝ)) := by {
    intro x
    simp [Set.Iic, setOf]
    exact Real.decidableLE x (-2)
  }
  apply womp luigi1 luigi2
  ext x
  simp
  intro h
  linarith

  ext x
  simp

#check Function.Constant
