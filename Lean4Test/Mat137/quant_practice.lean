import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Equiv.Defs

def shmincreasing (f : ℝ → ℝ) := ∀ x : ℝ, ∃ y : ℝ, x < y ∧ f x < f y
def shmdecreasing (f : ℝ → ℝ) := ∀ x : ℝ, ∃ y : ℝ, x < y ∧ f x > f y
def increasing (f : ℝ → ℝ) := ∀ x y : ℝ, x < y → f x < f y
def decreasing (f : ℝ → ℝ) := ∀ x y : ℝ, x < y → f x > f y
def constant (f : ℝ → ℝ) := ∃ C : ℝ, ∀ x : ℝ, f x = C
example : ∃ f : ℝ → ℝ, shmincreasing f ∧ ¬ increasing f := by
  use (fun x => x^2)
  apply And.intro
  intro x
  use |x| + 1
  use (by linarith [le_abs_self x])
  simp only
  have : x < |x| + 1 := by linarith [le_abs_self x]
  ring_nf
  rw [sq_abs x]
  linarith [abs_nonneg x]

  simp only [increasing, not_forall, not_lt, exists_prop]
  use (-1)
  use 0
  exact ⟨by norm_num, by norm_num⟩


#check FloorRing.floor
example : ∃ f : ℝ → ℝ, ¬ constant f  ∧ ¬ increasing f ∧ ¬ shmincreasing f ∧ ¬ decreasing f := by
  use (fun x => ite (FloorRing.floor x = x) 0 1)
  have w : FloorRing.floor ((1 / 2):ℝ) = 0 := by {
    apply Int.floor_eq_iff.mpr
    simp
    norm_num
  }

  apply And.intro
  intro ⟨C, hC⟩
  have crux := hC 0
  simp at crux
  have := hC (1/2)
  simp only [Int.floorRing_floor_eq] at this
  simp only [Int.floorRing_floor_eq] at w
  simp only [w] at this
  simp at this
  linarith

  apply And.intro
  intro h
  specialize h 0 1 (by linarith)
  simp at h

  apply And.intro
  intro h
  specialize h (1/2)
  match h with
  | ⟨y, hxy, H⟩ => {
    simp only at H
    simp only [w] at H
    simp at H
    cases ite_eq_or_eq (↑⌊y⌋ = y) (0:ℝ) 1 with
    | inl l => {
      rw [l] at H
      linarith
    }
    | inr r => {
      rw [r] at H
      linarith
    }
  }

  intro h
  specialize h 0 1 (by linarith)
  simp at h

example : ¬ (∃ f : ℝ → ℝ, shmincreasing f ∧ ∃ c : ℝ, ∀ x : ℝ, f x ≤ f c) := by
  intro ⟨f, ⟨hS, hM⟩⟩
  match hM with
  | ⟨c, hC⟩ => {
    specialize hS c
    match hS with
    | ⟨y, _, Hy⟩ => {
      specialize hC y
      linarith
    }
  }

#check exists_deriv_eq_slope
#check Continuous
example (f : ℝ → ℝ) : Differentiable ℝ f → shmincreasing f → ∀ x : ℝ, ∃ y : ℝ, deriv f y > 0 := by
  intros hD hS
  intro x
  specialize hS x
  match hS with
  | ⟨y₁, hy1, H⟩ => {
    have : Continuous f := Differentiable.continuous hD
    have := exists_deriv_eq_slope f hy1 (Continuous.continuousOn this) (Differentiable.differentiableOn hD)
    match this with
    | ⟨c, _, Hc⟩ => {
      use c
      rw [Hc]
      exact div_pos (by linarith) (by linarith)
    }
  }

#check Infinite
#check Nonempty
#check Equiv
#check WithBot
#check Infinite.natEmbedding
#check Infinite.of_injective_to_set
theorem Set.Infinite_of (S : Set ℝ) : (S.Nonempty ∧ ∀ x ∈ S, ∃ y ∈ S, x < y) → S.Infinite := by
  intro ⟨h1, h2⟩
  rw [Set.Infinite]
  intro hF
  have := Set.Finite.exists_maximal_wrt (fun x => x) S hF h1
  match this with
  | ⟨a, ha, H⟩ => {
    specialize h2 a ha
    match h2 with
    | ⟨y, hy, Hy⟩ => {
      specialize H y hy
      simp at H
      specialize H (le_of_lt Hy)
      linarith
    }
  }


example (f : ℝ → ℝ) (hC : Continuous f) : shmincreasing f → shmdecreasing f → ∃ c : ℝ, {x | f x = c}.Infinite := by
  intros hsinc hsdec
  use f 0
  apply Set.Infinite_of
  apply And.intro
  use 0
  simp

  intros x hx
  simp at hx
  specialize hsinc x
  specialize hsdec x
  match hsinc, hsdec with
  | ⟨y1, hy1, H1⟩, ⟨y2, hy2, H2⟩ => {
    have : f y1 ≠ f y2 := by linarith
    have : y1 ≠ y2 := ne_of_apply_ne (fun y1 => f y1) this
    have w : f x ∈ Set.Ioo (f y2) (f y1) := by {
      simp
      exact ⟨H2, H1⟩
    }
    cases Ne.lt_or_lt this with
    | inl l => {
      have := intermediate_value_Ioo' (le_of_lt l) (Continuous.continuousOn hC)
      specialize this w
      simp at this
      match this with
      | ⟨y, hy, Hy⟩ => {
        use y
        simp
        apply And.intro
        linarith only [hx, Hy]
        linarith only [hy1, hy]
      }
    }
    | inr r => {
      have := intermediate_value_Ioo (le_of_lt r) (Continuous.continuousOn hC)
      specialize this w
      simp at this
      match this with
      | ⟨y, hy, Hy⟩ => {
        use y
        simp
        apply And.intro
        linarith only [hx, Hy]
        linarith only [hy2, hy]
      }
    }
  }

#check intermediate_value_Ioo
