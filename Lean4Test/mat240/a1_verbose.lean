import Mathlib.Algebra.Field.Defs
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-
A1 of MAT240

verbose version: designed to give as much insight into the
related areas of mathlib
a lot of detours and exploration
-/

section q1q2

variables (F : Type*) [Field F]

example (a : F) : -(-a) = a :=
  neg_neg a

example (a : F) : a * 0 = 0 :=
  mul_zero a

end q1q2

section q3

#check Complex

open Complex

-- note that if defined `F` as a subtype of `ℂ`, then we would need axiom of skolkem to actually extract x.a and x.b from x
-- which would mean that we can't construct +, ⬝, ⁻¹ as functions but rather only prove that they exist
-- this is because `Prop` can only eliminate into `Prop`
structure F : Type where
  a : ℝ
  b : ℝ

-- instead we simply show that `F` can b embedded into `ℂ`
noncomputable def F.toComplex : F → ℂ := fun ⟨a, b⟩ => a + b * Real.sqrt 2 * I

def F.add : F → F → F := fun ⟨a, b⟩ ⟨c, d⟩ => ⟨a + c, b + d⟩
def F.mul : F → F → F :=  fun ⟨a, b⟩ ⟨c, d⟩ => ⟨a * c - 2 * b * d, a * d + b * c⟩
def F.neg : F → F := fun ⟨a, b⟩ => ⟨-a, -b⟩

-- motivation
-- fix (a, b), find (c, d)
-- we want (a + b√(-2)) • (c + d√(-2)) = (a * c - 2 * b * d) + (a * d + b * c)√(-2) = 1
-- solve the linear system
-- ac - 2bd = 1 -- (a)
-- ad + bc = 0 -- (b)

-- abc - 2b^2d = b, a^2d + abc = 0 → (a^2 + 2b^2)d = -b
-- a^2c - 2abd = a, 2abd + 2b^2c = 0 → (a^2 + 2b^2) c = a

-- otherwise, when a^2 + 2b^2 = 0
-- it must be that a = 0 and b = 0

noncomputable def F.inv : F → F := fun ⟨a, b⟩ => ⟨a / (a ^ 2 + 2 * b ^ 2), - b / (a^2 + 2 * b^2)⟩

instance : Add F :=
  ⟨F.add⟩
instance : Zero F :=
  ⟨⟨0, 0⟩⟩
instance : Mul F :=
  ⟨F.mul⟩
instance : One F :=
  ⟨1, 0⟩
instance : Neg F :=
  ⟨F.neg⟩

noncomputable instance : Inv F :=
  ⟨F.inv⟩

example : (1 : F).toComplex = (1 : ℂ) := by
  simp only [F.toComplex, ofReal_one, ofReal_zero, zero_mul, add_zero]

example : (0 : F).toComplex = (0 : ℂ) := by
  simp only [F.toComplex, ofReal_one, ofReal_zero, zero_mul, add_zero]


def F.add_def (x y : F) : x + y = ⟨x.a + y.a, x.b + y.b⟩ := by rfl
def F.mul_def (x y : F) : x * y = ⟨x.a * y.a - 2 * x.b * y.b, x.a * y.b + x.b * y.a⟩ := by rfl
def F.neg_def (x : F) : -x = ⟨-x.a, -x.b⟩ := by rfl
def F.ext (x : F) : x = ⟨x.a, x.b⟩ := by rfl

-- sanity check the field extension is faifthul
example (x y : F) : (x + y).toComplex = x.toComplex + y.toComplex := by {
  rw [F.add_def]
  simp only [F.toComplex]
  push_cast
  ring
}

-- def F.mul : F → F → F :=

def F.zero_a : (0 : F).a = 0 := by rfl
def F.zero_b : (0 : F).b = 0 := by rfl
def F.zero_eq : (0 : F) = ⟨0, 0⟩ := by rfl

def F.one_a : (1 : F).a = 1 := by rfl
def F.one_eq : (1 : F) = ⟨1, 0⟩ := by rfl
def F.one_b : (1 : F).b = 0 := by rfl

def F.add_a (x y : F) : (x + y).a = x.a + y.a := by rfl
def F.add_b (x y : F) : (x + y).b = x.b + y.b := by rfl

theorem F.mul_inv (a : F) (ha : a ≠ (0:F)) : a * a⁻¹ = 1 := by
  simp only [Inv.inv, F.inv]
  cases em (a.a^2 + 2*a.b^2 = 0) with
  | inl l =>
    rw [F.one_eq]
    have w1 : a.a = 0 := by
      apply by_contradiction
      intro h
      linarith [(sq_pos_iff a.a).mpr h, sq_nonneg a.a, sq_nonneg a.b]
    have w2: a.b = 0 := by
      simp [w1] at l
      exact l
    exact False.elim <| ha (congr_arg₂ F.mk w1 w2)
  | inr r =>
    simp [F.one_eq, F.mul_def]
    apply And.intro
    all_goals
      field_simp
      ring

theorem F.inv_zero : (0 : F)⁻¹ = (0:F) := by
  simp [Inv.inv, F.inv, F.zero_eq]

noncomputable instance : Field F :=
{
  add := fun ⟨a, b⟩ ⟨c, d⟩ => ⟨a + c, b + d⟩
  add_assoc := by
    intro a b c
    simp only [F.add_def]
    ring
  zero_add := by
    intro a
    simp only [F.add_def, F.zero_a, F.zero_b]
    ring
  add_zero := by
    intro a
    simp only [F.add_def, F.zero_a, F.zero_b]
    ring
  add_comm := by
    intro a b
    simp only [F.add_def]
    ring
  left_distrib := by
    intro a b c
    simp only [F.mul_def, F.add_def, F.add_a, F.add_b]
    ring
  right_distrib := by
    intro a b c
    simp only [F.mul_def, F.add_def, F.add_a, F.add_b]
    ring
  zero_mul := by
    intro a
    simp only [F.mul_def, F.zero_a, F.zero_b]
    ring; rfl
  mul_zero := by
    intro a
    simp only [F.mul_def, F.zero_a, F.zero_b]
    ring; rfl
  mul_assoc := by
    intro a b c
    simp only [F.mul_def]
    ring
  one_mul := by
    intro a
    simp only [F.mul_def, F.one_a, F.one_b]
    ring
  mul_one := by
    intro a
    simp only [F.mul_def, F.one_a, F.one_b]
    ring
  add_left_neg := by
    intro a
    simp only [F.neg_def, F.add_def]
    ring; rfl
  mul_comm := by
    intro a b
    simp only [F.neg_def, F.add_def, F.mul_def]
    ring
  exists_pair_ne := by
    use 0; use 1
    intro h
    have : (0 : F).a = (1 : F).a := by exact congrArg F.a h
    simp [F.zero_a, F.one_a] at this
  mul_inv_cancel := F.mul_inv
  inv_zero := F.inv_zero
}

end q3

namespace q4

-- in lean `[` `]` is used to denote lists
-- so we use `⟦` `a` `⟧` to denote the equivalence class on `a`

#check Quotient
-- `Quotient` gives quotient of a type `α` with respect to an equivalence relation `≈`
-- the defining equation for `Quotient` is `Quotient.eq`
-- ⟦x⟧ = ⟦y⟧ ↔ x ≈ y

-- in the case of modular arithmetic `a ≈ b := (a - b) % p = 0`
-- for this question, we are working in `ℤ₁₂`
-- so we're gonna give the integer the equivalence relation `a ≈ b := (a - b) % 12 = 0`
instance z12 : Setoid ℤ :=
{
  r := fun a b => (a - b) % 12 = 0
  iseqv := by {
    apply Equivalence.mk
    simp

    simp
    intro x y hxy
    exact dvd_sub_comm.mp hxy

    simp
    intro x y z hxy hyz
    have : 12 ∣ (x - y) + (y - z) :=
      Int.dvd_add hxy hyz
    simp at this
    exact this
  }
}
abbrev ℤ₁₂ := Quotient z12

#check (⟦2⟧ : Quotient z12)

def add_equiv_add {a b c d : ℤ} : a ≈ c → b ≈ d → a + b ≈ c + d := by
  intro h1 h2
  simp [HasEquiv.Equiv, Setoid.r] at *
  have : 12 ∣ (a - c) + (b - d) := Int.dvd_add h1 h2
  have w : a - c + (b - d) = (a + b) - (c + d) := by ring
  rw [w] at this
  exact this

def mul_equiv_mul {a b c d : ℤ} : a ≈ c → b ≈ d → a * b ≈ c * d := by
  intro h1 h2
  simp [HasEquiv.Equiv, Setoid.r] at *
  have w1 : 12 ∣ b * (a - c) :=
    Dvd.dvd.mul_left h1 b
  have w2 : 12 ∣ c * (b - d) :=
    Dvd.dvd.mul_left h2 c
  have : 12 ∣ b * (a - c) + c * (b - d) :=
    Int.dvd_add w1 w2
  have woo : b * (a - c) + c * (b - d)  = a * b - c * d := by ring
  rw [woo] at this
  exact this

instance : Add (Quotient z12) :=
  ⟨(Quotient.map₂ (· + ·)) fun _ _ hf _ _ hg => add_equiv_add hf hg⟩

instance : Mul (Quotient z12) :=
  ⟨(Quotient.map₂ (· * ·)) fun _ _ hf _ _ hg => mul_equiv_mul hf hg⟩

instance : Neg (Quotient z12) :=
  ⟨fun x => ⟦-1⟧ * x⟩

def mk_mul (a b : ℤ) : (⟦a⟧: Quotient z12) * ⟦b⟧ = ⟦a * b⟧ := by rfl
def mk_add (a b : ℤ) : (⟦a⟧: Quotient z12) + ⟦b⟧ = ⟦a + b⟧ := by rfl
def mk_neg (a : ℤ) : -(⟦a⟧: Quotient z12) = ⟦-a⟧ := by
  simp only [Neg.neg, show Int.neg 1 = -1 by rfl, mk_mul, neg_mul, one_mul]



-- a) has solution
-- want ⟦5⟧ x = ⟦4⟧
-- 5 * 8 = 40 ≈ 4
example (x : ℤ₁₂) : (⟦5⟧ :  ℤ₁₂) * x + ⟦3⟧ = (⟦7⟧ : ℤ₁₂) ↔ x = (⟦8⟧ : ℤ₁₂):= by
  apply Iff.intro
  intro h
  match x.exists_rep with
  | ⟨x', hx⟩ => {
    rw [← hx, mk_mul, mk_add, Quotient.eq] at h
    simp [HasEquiv.Equiv, Setoid.r] at h
    have : 5 * x' + 3 - 7 = 5 * (x' - 8) + 3 * 12 := by ring
    rw [this] at h
    rw [← hx, Quotient.eq]
    simp [HasEquiv.Equiv, Setoid.r]
    exact Int.dvd_of_dvd_mul_right_of_gcd_one ((Int.dvd_add_left ⟨3, by rfl⟩).mp h) (by rfl)
  }
  intro h
  rw [h]
  simp [mk_mul, mk_add, HasEquiv.Equiv, Setoid.r]

-- b) has solution
-- we want 12 ∣ (3x + 6) = 3(x + 2)
-- so x + 2 is divisible by 4
theorem q4b_aux (x : ℤ) : (⟦3⟧ :  ℤ₁₂) * ⟦x⟧ + ⟦11⟧ = (⟦5⟧ : ℤ₁₂) ↔ 4 ∣ (x + 2) := by
  simp [mk_mul, mk_add, HasEquiv.Equiv, Setoid.r]
  rw [show 3 * x + 11 - 5 = 3 * (x + 2) by ring,
      show 12 = 3 * (4 : ℤ) by ring]
  have w : 4 ∣ (x + 2) → 3 * 4 ∣ 3 * (x + 2) := by exact fun a => mul_dvd_mul_left 3 a
  have w1 : 3 * 4 ∣ 3 * (x + 2)  → 4 ∣ 3 * (x + 2) := by exact fun a => dvd_of_mul_left_dvd a
  have w1' : 4 ∣ 3 * (x + 2) → 4 ∣ (x + 2) :=
   fun a => Int.dvd_of_dvd_mul_right_of_gcd_one a (by rfl)
  rw [← Iff.intro w (w1' ∘ w1)]

theorem q4b_full_cond (x : ℤ₁₂) : (⟦3⟧ :  ℤ₁₂) * x + ⟦11⟧ = (⟦5⟧ : ℤ₁₂) ↔ x = ⟦2⟧ ∨ x = ⟦6⟧ ∨ x = ⟦10⟧ :=
    (fun p x => x p) x.exists_rep <| fun ⟨x', hx⟩ => by
  simp [← hx, q4b_aux, HasEquiv.Equiv, Setoid.r]
  apply Iff.intro

  · intro ⟨k, hk⟩
    have w1 : x' + 2 ≡ x' + -10 [ZMOD 4 * 3] := Int.ModEq.add rfl (by rfl)

    mod_cases h : k % 3
    · have : 4 * k ≡ 4 * 0 [ZMOD (4 * 3)] := Int.ModEq.mul_left' h
      simp [← hk] at this
      apply Or.inr ∘ Or.inr ∘ Int.modEq_zero_iff_dvd.mp
      exact show x' + -10 ≡ 0 [ZMOD 4 * 3] from
        Int.ModEq.trans (id (Int.ModEq.symm w1)) this
    · have wee : 4 * k ≡ 4 * 1 [ZMOD (4 * 3)] := Int.ModEq.mul_left' h
      simp [← hk] at wee
      apply Or.inl ∘ Int.ModEq.dvd ∘ id ∘ Int.ModEq.symm
      exact show  x' ≡ 10 + 4 [ZMOD 4 * 3]
        from Int.ModEq.add_right_cancel rfl wee
    · have wee : 4 * k ≡ 4 * 2 [ZMOD (4 * 3)] := Int.ModEq.mul_left' h
      rw [← hk] at wee
      apply Or.inr ∘ Or.inl ∘ Int.ModEq.dvd ∘ id ∘ Int.ModEq.symm
      exact show x' ≡ 10 + 4 * 2 [ZMOD 4 * 3]
        from Int.ModEq.add_right_cancel rfl wee
  · intro h
    apply Or.elim3 h
    · intro ⟨k, hk⟩
      use (3*k + 1)
      linarith
    · intro ⟨k, hk⟩
      use (3 * k + 2)
      linarith
    · intro ⟨k, hk⟩
      use (3 * k + 3)
      linarith

-- c) has solution
-- ⟦x⟧^2 = -⟦11⟧
-- ⟦x⟧^2 - ⟦1⟧ = 0
-- (⟦x⟧ - ⟦1⟧) * (⟦x⟧ + ⟦1⟧) = 0
-- 12 ∣ (x - 1) * (x + 1)
-- so we have :
-- 1 ∣ (x + 1), 12 ∣ (x - 1)
-- 3 ∣ (x + 1), 4 ∣ (x - 1)
-- 2 ∣ (x + 1), 6 ∣ (x - 1)
-- 6 ∣ (x + 1), 2 ∣ (x - 1)
-- 4 ∣ (x + 1), 3 ∣ (x - 1)
-- 12 ∣ (x + 1), 1 ∣ (x - 1)
-- -11 ≈ 1
-- we can use 5 since 5^2 = 25 ≈ 1
theorem q4c_aux1 (x : ℤ) : ⟦x⟧ * ⟦x⟧  = -(⟦11⟧ : ℤ₁₂) ↔ 12 ∣ (x + 1) * (x - 1) := by
  calc
    _ ↔ ⟦x * x + -1⟧ = (⟦0⟧:Quotient z12) := by
      rw [mk_mul]
      have : -(⟦11⟧ : Quotient z12) = (⟦1⟧:Quotient z12) := by
        simp [Neg.neg, mk_mul, HasEquiv.Equiv, Setoid.r]
      rw [this]
      simp [HasEquiv.Equiv, Setoid.r]
      ring_nf
    _ ↔ 12 ∣ (x + 1) * (x - 1) := by
      simp [HasEquiv.Equiv, Setoid.r]
      ring_nf

theorem Or.elim6 (A1 A2 A3 A4 A5 A6 P : Prop) (h1 : A1 → P) (h2 : A2 → P) (h3 : A3 → P) (h4 : A4 → P) (h5 : A5 → P) (h6 : A6 → P) : (A1 ∨ A2 ∨ A3 ∨ A4 ∨ A5 ∨ A6) → P := by {
  tauto
}

theorem Or.elim6' {A1 A2 A3 A4 A5 A6 P : Prop} (H : A1 ∨ A2 ∨ A3 ∨ A4 ∨ A5 ∨ A6) (h1 : A1 → P) (h2 : A2 → P) (h3 : A3 → P) (h4 : A4 → P) (h5 : A5 → P) (h6 : A6 → P) : P := by {
  tauto
}


theorem q4c_aux2 (x : ℤ) :12 ∣ (x + 1) * (x - 1) ↔
  1 ∣ (x + 1) ∧ 12 ∣ (x - 1) ∨
  3 ∣ (x + 1) ∧ 4 ∣ (x - 1) ∨
  2 ∣ (x + 1) ∧ 6 ∣ (x - 1) ∨
  6 ∣ (x + 1) ∧ 2 ∣ (x - 1) ∨
  4 ∣ (x + 1) ∧ 3 ∣ (x - 1) ∨
  12 ∣ (x + 1) ∧ 1 ∣ (x - 1) := by
  {
    apply Iff.intro
    · intro h
      -- rw [dvd_mul] at h
      have : (12 : ℤ).natAbs ∣ ((x + 1) * (x - 1)).natAbs :=
        Int.natAbs_dvd_natAbs.mpr h
      rw [Int.natAbs_mul (x + 1) (x - 1)] at this
      rw [dvd_mul] at this
      match this with
      | ⟨d₁, d₂, H⟩ => {
        have :  d₁ ∈ Nat.divisors 12 := by
          have h := H.2.2
          rw [show Int.natAbs 12 = 12 by rfl] at h
          simp
          use d₂
        have crux : Nat.divisors 12 = {Int.natAbs 1, Int.natAbs 2, Int.natAbs 3, Int.natAbs 4, Int.natAbs 6, Int.natAbs 12} := by rfl
        rw [crux] at this
        simp only [Finset.mem_singleton, Finset.mem_insert] at this
        have wow := H.2.2
        apply Or.elim6' this
        · intro h
          have : d₂ = Int.natAbs 12 := by
            rw [h] at wow
            simp [Int.natAbs] at *
            linarith
          rw [h, this] at H
          exact Or.inl <|
            ⟨Int.natAbs_dvd_natAbs.mp H.1, Int.natAbs_dvd_natAbs.mp H.2.1⟩
        · intro h
          have : d₂ = Int.natAbs 6 := by
            rw [h] at wow
            simp [Int.natAbs] at *
            linarith
          rw [h, this] at H
          exact Or.inr ∘ Or.inr ∘ Or.inl <|
            ⟨Int.natAbs_dvd_natAbs.mp H.1, Int.natAbs_dvd_natAbs.mp H.2.1⟩
        · intro h
          have : d₂ = Int.natAbs 4 := by
            rw [h] at wow
            simp [Int.natAbs] at *
            linarith
          rw [h, this] at H
          have : 4 ∣ (x - 1) :=
            Int.natAbs_dvd_natAbs.mp H.2.1
          have : 3 ∣ (x + 1) :=
            Int.natAbs_dvd_natAbs.mp H.1
          tauto
        · intro h
          have : d₂ = Int.natAbs 3 := by
            rw [h] at wow
            simp [Int.natAbs] at *
            linarith
          rw [h, this] at H
          exact Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl <|
            ⟨Int.natAbs_dvd_natAbs.mp H.1, Int.natAbs_dvd_natAbs.mp H.2.1⟩
        · intro h
          have : d₂ = Int.natAbs 2 := by
            rw [h] at wow
            simp [Int.natAbs] at *
            linarith
          rw [h, this] at H
          exact Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl <|
            ⟨Int.natAbs_dvd_natAbs.mp H.1, Int.natAbs_dvd_natAbs.mp H.2.1⟩
        · intro h
          have : d₂ = Int.natAbs 1 := by
            rw [h] at wow
            simp [Int.natAbs] at *
            linarith
          rw [h, this] at H
          exact Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr <|
            ⟨Int.natAbs_dvd_natAbs.mp H.1, Int.natAbs_dvd_natAbs.mp H.2.1⟩
      }

    apply Or.elim6
    all_goals
    · intro ⟨h1, h2⟩
      exact mul_dvd_mul h1 h2
  }

theorem q4c_aux_1_12 (x : ℤ) : 1 ∣ (x + 1) ∧ 12 ∣ (x - 1) ↔ 12 ∣ (x - 1) := by {
  have : 1 ∣ x + 1 := by exact one_dvd (x + 1)
  tauto
}
-- x + 1 = 3, 6, 9, 12 ↔ x = 2, 5, 8, 11
-- x - 1 = 4, 8, 12 ↔ x = 5, 9, 1

-- a = 2, b = 6
-- 2 ∣ (x + 1), 6 ∣ (x - 1)
-- 4 * x ≡ -8
-- x ≡ -2
theorem q4c_aux_a_b (x : ℤ) (a b : ℤ) : a ∣ (x + 1) ∧ b ∣ (x - 1) → (b - a) / gcd a b * x ≡ -(a + b) / gcd a b [ZMOD a * b / gcd a b]  := by {
  · intro h
    have := h.left
    have : (x + 1) ≡ 0 [ZMOD a] :=
      Dvd.dvd.modEq_zero_int h.left
    have H1 : (b / gcd a b) * (x + 1) ≡ (b / gcd a b) * 0 [ZMOD (b / (gcd a b)) * a] :=
      Int.ModEq.mul_left' this
    have : (x - 1) ≡ 0 [ZMOD b] :=
      Dvd.dvd.modEq_zero_int h.right
    have H2 : (a / gcd a b) * (x - 1) ≡ (a / gcd a b) * 0 [ZMOD ((a / gcd a b) * b)] :=
      Int.ModEq.mul_left' this
    rw [show (b / gcd a b) * a = a * b / gcd a b by {
      rw [mul_comm, Int.mul_ediv_assoc _ (gcd_dvd_right a b)]
    }] at H1
    rw [show (a / gcd a b) * b = a * b / gcd a b by {
      rw [mul_comm, ← Int.mul_ediv_assoc _ (gcd_dvd_left a b), mul_comm]
    }] at H2
    rw [mul_zero] at *
    have : b / (gcd a b) * (x + 1) ≡ a / (gcd a b) * (x - 1) [ZMOD (a * b) / gcd a b] :=
      Int.ModEq.trans H1 (id (Int.ModEq.symm H2))
    have : (a * b / gcd a b) ∣ (b / gcd a b * (x + 1) - a / gcd a b * (x - 1)) :=
      Int.ModEq.dvd (id (Int.ModEq.symm this))
    have w : b / gcd a b * (x + 1) - a / gcd a b * (x - 1) = (b - a) / gcd a b  * x - - (a + b) / gcd a b := by {
      sorry
    }
    rw [w, ← Int.modEq_iff_dvd] at this
    exact id (Int.ModEq.symm this)
}

example (x : ℤ) : 1 ∣ (x + 1) ∧ 12 ∣ (x - 1) ↔ x ≡ 1 [ZMOD 12] := by
  have : 1 ∣ (x + 1) := one_dvd (x + 1)
  simp [this]
  rw [Int.modEq_iff_dvd]
  apply Iff.intro
  all_goals
    intro h
    exact dvd_sub_comm.mp h

example (x : ℤ) : 12 ∣ (x + 1) ∧ 1 ∣ (x - 1) ↔ x ≡ 11 [ZMOD 12] := by
  simp [one_dvd (x - 1)]
  rw [Int.modEq_iff_dvd]
  apply Iff.intro
  · intro h
    -- dvd_sub_comm.mp h
    have : 12 ∣ 12 - (x + 1) := by
      rw [dvd_sub_self_left]
      exact h
    ring_nf at this
    exact this
  · intro h
    have : 12 ∣ 12 - (11 - x) := by
      rw [dvd_sub_self_left]
      exact h
    ring_nf at this
    rw [add_comm] at this
    exact this

example (x : ℤ) : 2 ∣ (x + 1) ∧ 6 ∣ (x - 1) ↔ x ≡ 1 [ZMOD 12] ∨ x ≡ 7 [ZMOD 12] := by
apply Iff.intro
· intro h
  have := q4c_aux_a_b _ _  _ h
  rw [show gcd (2 : ℤ) 6  = 2 by rfl] at this
  norm_num [show (4:ℤ) / 2 = 2 by rfl, show (-8:ℤ) / 2 = -4 by rfl, show (12:ℤ) / 2 = 6 by rfl] at this
  rw [Int.modEq_iff_dvd, show -4 -2* x = -2*(x + 2) by ring, neg_mul, dvd_neg, show (6 : ℤ) = 2 * 3 by rfl] at this
  rw [mul_dvd_mul_iff_left (by simp only)] at this
  match this with
  | ⟨k, hk⟩ =>
    mod_cases k % 4
    · rw [Int.modEq_iff_dvd, show 0 - k = -k by ring, dvd_neg] at H
      match H with
      | ⟨k', hk'⟩ =>
        have : x + 1 = 2 * (6 * k') + (-1) := by linarith
        rw [this] at h
        have : 2 ∣ 2 * (6 * k') :=
          Int.dvd_mul_right 2 (6 * k')
        rw [dvd_add_right this] at h
        simp at h
    · rw [Int.modEq_iff_dvd, show 1 - k = -(k - 1) by ring, dvd_neg] at H
      match H with
      | ⟨k', hk'⟩ =>
        have : x = 3 * k - 2 := by linarith
        have w : k = 4*k' + 1 := by linarith
        apply Or.inl
        rw [Int.modEq_iff_dvd, this, w, show 1 - (3 * (4 * k' + 1) - 2) = - (12 * k') by ring, dvd_neg]
        exact Int.dvd_mul_right 12 k'
    · rw [Int.modEq_iff_dvd, show 2 - k = -(k - 2) by ring, dvd_neg] at H
      match H with
      | ⟨k', hk'⟩ =>
        have : x - 1 = 6 * (2 * k') + 3 := by linarith
        have hh := h.right
        rw [this, dvd_add_right] at hh
        simp only at hh
        exact Int.dvd_mul_right 6 (2 * k')
    · rw [Int.modEq_iff_dvd, show 3 - k = -(k - 3) by ring, dvd_neg] at H
      match H with
      | ⟨k', hk'⟩ =>
        have w1 : x = 3*k - 2 := by linarith
        have w2 : k = 4 * k' + 3 := by linarith
        apply Or.inr
        rw [Int.modEq_iff_dvd, w1, w2]
        ring_nf
        rw [mul_comm, dvd_neg]
        exact Int.dvd_mul_right 12 k'
· intro h
  cases h with
  | inl l =>
    rw [Int.modEq_iff_dvd, show (12 : ℤ) = (6 * 2) by rfl, dvd_sub_comm] at l
    apply And.intro
    · have : 2 ∣ (x - 1) + 2 :=
        Int.dvd_add (dvd_of_mul_left_dvd l) (Int.dvd_refl 2)
      rw [show (x - 1) + 2 = x + 1 by ring] at this
      exact this
    exact dvd_of_mul_right_dvd l
  | inr r =>
    rw [Int.modEq_iff_dvd, show (12 : ℤ) = (6 * 2) by rfl, dvd_sub_comm] at r
    apply And.intro
    · have : 2 ∣ x - 7 := dvd_of_mul_left_dvd r
      rw [show x + 1 = x - 7 + 8 by ring, dvd_add_right this]
      simp only
    · have : 6 ∣ x - 7 := dvd_of_mul_right_dvd r
      rw [show x - 1 = x - 7 + 6 by ring, dvd_add_right this]

example (x : ℤ) : 3 ∣ (x + 1) ∧ 4 ∣ (x - 1) ↔ x ≡ 5 [ZMOD 12]  := by
apply Iff.intro
· intro h
  apply q4c_aux_a_b _ _ _ at h
  norm_num [show gcd (3:ℤ) 4 = 1 by rfl] at h
  exact h

· intro h
  rw [Int.modEq_iff_dvd, show (12 : ℤ) = 3 * 4 by rfl] at h
  have h3 := dvd_of_mul_right_dvd h
  have h4 := dvd_of_mul_left_dvd h
  apply And.intro
  · have : 3 ∣ 6 - (5 - x) := by exact Int.dvd_sub (show 3 ∣ (6:ℤ) by simp only) h3
    rw [show 6 - (5 - x) = x + 1 by ring] at this
    exact this
  · have : 4 ∣ 4 - (5 - x) := by exact Int.dvd_sub (show 4 ∣ (4:ℤ) by simp only) h4
    rw [show 4 - (5 - x) = x - 1 by ring] at this
    exact this

example (x : ℤ) : 4 ∣ (x + 1) ∧ 3 ∣ (x - 1) ↔ x ≡ 7 [ZMOD 12]  := by
  apply Iff.intro
  intro h
  apply q4c_aux_a_b _ _ _ at h
  norm_num [show gcd (4:ℤ) 3 = 1 by rfl] at h
  exact h

theorem equiv_sub {p a b c : ℤ} (h : b ≡ c [ZMOD p] ) : b ≡ a [ZMOD p] ↔ c ≡ a [ZMOD p] := by sorry

-- proof for 4 c): done using case bash with 12 cases
-- the helper lemmas weren't used but help to get a better understanding of the problem space
-- would be necessary for larger moduluses tho
example (x : ℤ) : x^2 ≡ -11 [ZMOD 12] ↔ x ≡ 1 [ZMOD 12] ∨ x ≡ 5 [ZMOD 12] ∨ x ≡ 7 [ZMOD 12] ∨ x ≡ 11 [ZMOD 12]:= by
  have temp {a : ℤ} (hx : x ≡ a [ZMOD 12]) : x^2 ≡ a^2 [ZMOD 12] :=
    Int.ModEq.pow 2 hx
  mod_cases x % 12
  all_goals
  · rw [equiv_sub <| temp H]
    simp only [equiv_sub H]

-- q4 a) with similar case bash optimization
example (x : ℤ) : 5 * x + 3 ≡ 7 [ZMOD 12] ↔ x ≡ 8 [ZMOD 12] := by
  have temp {a : ℤ} (hx : x ≡ a [ZMOD 12]) : 5 * x + 3 ≡ 5 * a + 3 [ZMOD 12] := by
    have : 5 * x ≡ 5 * a [ZMOD 12] :=
      Int.ModEq.mul rfl hx
    exact Int.ModEq.add this rfl
  mod_cases x % 12
  · all_goals
    simp only [equiv_sub <| temp H, equiv_sub H]

-- q4 b) with similar case bash optimization
example (x : ℤ) : 3 * x + 11 ≡ 5 [ZMOD 12] ↔ x ≡ 2 [ZMOD 12]  ∨ x ≡ 6 [ZMOD 12] ∨ x ≡ 10 [ZMOD 12] := by
  have temp {a : ℤ} (hx : x ≡ a [ZMOD 12]) : 3*x + 11 ≡ 3*a + 11 [ZMOD 12] := by
    have : 3 * x ≡ 3 * a [ZMOD 12] :=
      Int.ModEq.mul rfl hx
    exact Int.ModEq.add this rfl
  mod_cases x % 12
  all_goals
  · rw [equiv_sub <| temp H]
    simp only [equiv_sub H]

end q4

section q5q6

def r (n : ℤ) (x y : ℤ) : Prop := n ∣ (x - y)

instance lmao {n : ℤ} : Equivalence (r n) :=
{
  refl := by
    simp only [r, sub_self, dvd_zero, forall_const]
  symm := by
    intro x y h
    exact dvd_sub_comm.mp h
  trans := by
    simp [r]
    intro x y z h1 h2
    have : n ∣ (x - y) + (y - z) :=
      Int.dvd_add h1 h2
    ring_nf at this
    exact this
}

example (n : ℤ) : Equivalence (r n) := lmao

example (n : ℤ) : Equivalence (r n) := inferInstance
/-
type class instance expected
  Equivalence (r n)
-/

-- need to use Quot instead of Quotient so we can use multiple equivalence relations on the same type `ℤ`
def F.mul_equiv_mul {n : ℤ} {a b c d : ℤ} : r n a c → r n b d → r n (a * b) (c * d) := by
  intro h1 h2
  have w1 : n ∣ b * (a - c) :=
    Dvd.dvd.mul_left h1 b
  have w2 : n ∣ c * (b - d) :=
    Dvd.dvd.mul_left h2 c
  have : n ∣ b * (a - c) + c * (b - d) :=
    Int.dvd_add w1 w2
  have woo : b * (a - c) + c * (b - d)  = a * b - c * d := by ring
  rw [woo] at this
  exact this

instance {n : ℤ} : Add (Quot (r n)) := {
  add := by {
    apply Quot.map₂ (· + ·)
    intro a b1 b2 h
    simp [r]
    ring_nf
    exact h

    intro a1 a2 b h
    simp [r]
    ring_nf
    exact h
  }
}

instance {n : ℤ} : Mul (Quot (r n))  := {
  mul := by {
    apply Quot.map₂ (· * ·)
    intro a b1 b2 h
    have w2 : n ∣ a * (b1 - b2) :=
      Dvd.dvd.mul_left h a
    ring_nf at w2
    exact w2

    intro a1 a2 b h
    have w2 : n ∣ (a1 - a2) * b :=
      Dvd.dvd.mul_right h b
    ring_nf at w2
    exact w2
  }
}

-- now prove theorem
theorem Int.gcd_eq_sum (x y : ℤ): ∃ (a : ℤ) (b : ℤ), a * x + b * y = Int.gcd x y := by sorry
theorem Int.gcd_le_sum (x y a b : ℤ) : Int.gcd x y ≤ a * x + b * y := by sorry

theorem mk_add {n : ℤ} (a b : ℤ) : Quot.mk (r n) a + Quot.mk (r n) b = Quot.mk (r n) (a + b) := by rfl
theorem mk_mul {n : ℤ} (a b : ℤ) : Quot.mk (r n) a * Quot.mk (r n) b = Quot.mk (r n) (a * b) := by rfl
-- x * x' - n * y = 1
-- ax + bn = gcd(x, n)
-- (x' - a)x + (b + y)n
#check Int.instDvdInt

-- proved condition for multiplicative inverses
example (n : ℤ) (x : ℤ) : Int.gcd n x = 1 ↔ ∃ x' : (Quot (r n)), (Quot.mk _ x : Quot (r n)) * x' = Quot.mk _ 1 := by {
  apply Iff.intro
  intro h
  match Int.gcd_eq_sum n x with
  | ⟨a, b, hab⟩ => {
    rw [h] at hab
    simp at hab
    use Quot.mk _ b
    rw [mk_mul, Quot.eq]
    apply EqvGen.rel (x * b) 1
    simp [r]
    exact Dvd.intro_left (-a) (by linarith)
  }

  intro ⟨x', hx'⟩
  match x'.exists_rep with
  | ⟨x'', hx''⟩ => {
    rw [← hx'', mk_mul, Quot.eq, Equivalence.eqvGen_eq, r] at hx'

    match hx' with
    | ⟨k, hk⟩ => {
      have : (-k) * n + x'' * x = 1 := by linarith
      have w := Int.gcd_le_sum n x (-k) x''
      rw [this] at w
      simp at w
      cases em (x = 0) with
      | inl l =>
        simp [l] at hx'
        rw [l]
        simp
        have : Int.natAbs n ∣ Int.natAbs (1 : ℤ) :=
          Int.natAbs_dvd_natAbs.mpr hx'
        simp only [Int.natAbs_one, Nat.isUnit_iff, Nat.dvd_one] at this
        exact this
      | inr r =>
        have : 0 < Int.gcd n x  := by
          rw [Int.gcd_pos_iff]
          exact Or.inr r
        have : Int.gcd n x ≥ 1 := by linarith
        exact le_antisymm w this
    }
    exact lmao
  }
}

def Smallest {α : Type*} [LE α] (p : α → Prop) (a : α) := p a ∧ ∀ b, p b → a ≤ b

instance {n : ℤ} : Zero (Quot (r n)) :=
  ⟨Quot.mk _ 0⟩
instance {n : ℤ} : One (Quot (r n)) :=
  ⟨Quot.mk _ 1⟩

theorem zero_eq : (0 : Quot (r n)) = Quot.mk _ 0 := by rfl

instance {n : ℤ} : Ring (Quot (r n)) := {
  add_assoc := by
    intro a b c
    match Quot.exists_rep a, Quot.exists_rep b, Quot.exists_rep c with
    | ⟨a', ha⟩, ⟨b', hb⟩, ⟨c', hc⟩ => {
      rw [← ha, ← hb, ← hc]
      simp [mk_add]
      ring
    }
  zero_add := by
    intro a
    simp [zero_eq]
    match Quot.exists_rep a with
    | ⟨a', ha⟩ =>
      rw [← ha, mk_add]
      ring
  add_zero := by
    intro a
    simp [zero_eq]
    match Quot.exists_rep a with
    | ⟨a', ha⟩ =>
      rw [← ha, mk_add]
      ring
  add_comm := by
    intro a b
    simp [zero_eq]
    match Quot.exists_rep a, Quot.exists_rep b with
    | ⟨a', ha⟩, ⟨b', hb⟩ =>
      rw [← ha, ← hb, mk_add, mk_add]
      ring
  left_distrib := by
    intro a b c
    match Quot.exists_rep a, Quot.exists_rep b, Quot.exists_rep c with
    | ⟨a', ha⟩, ⟨b', hb⟩, ⟨c', hc⟩ =>
      simp [← ha, ← hb, ← hc, mk_add, mk_mul]
      ring
  right_distrib := by
    intro a b c
    match Quot.exists_rep a, Quot.exists_rep b, Quot.exists_rep c with
    | ⟨a', ha⟩, ⟨b', hb⟩, ⟨c', hc⟩ =>
      simp [← ha, ← hb, ← hc, mk_add, mk_mul]
      ring
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry
  neg := by sorry
  add_left_neg := by sorry
}

theorem nsmul_bruh {p : Nat} (n : Nat) : AddMonoid.nsmul n (Quot.mk (r p) 1) = Quot.mk (r p) n := by {
  induction n with
  | zero => {
    rw [AddMonoid.nsmul_zero]
    simp [zero_eq]
  }
  | succ n ih => {
    rw [AddMonoid.nsmul_succ]
    rw [ih, mk_add]
    simp
    ring
  }
}

-- Q6 a) character of a ℤ[p]
-- Note would be better to use `charP` to make it more inline with mathlib4
example {p : Nat} (hp : p > 0): Smallest (fun (n : Nat) => AddMonoid.nsmul n (Quot.mk (r p) 1) = (0 : Quot (r p)) ∧ n > 0) p := by
{
  apply And.intro
  simp only
  rw [nsmul_bruh p, zero_eq]
  rw [Quot.eq]
  rw [Equivalence.eqvGen_eq]
  simp [r]
  exact hp

  exact lmao

  intro b h
  apply by_contradiction
  simp
  intro h'
  rw [nsmul_bruh, zero_eq, Quot.eq, Equivalence.eqvGen_eq] at h
  simp [r] at h
  have : p ∣ b := by exact Int.ofNat_dvd.mp h.1
  match this with
  | ⟨k, hk⟩ => {
    have w : k > 0 := by
      apply by_contradiction
      simp
      intro hw
      simp [hw] at hk
      linarith
    have : p = b / k := by exact (Nat.div_eq_of_eq_mul_left w hk).symm
    have : b / k ≤ b := Nat.div_le_self b k
    linarith
  }
  exact lmao
}


-- Q6 b) if a field has a non-zero characteristic, it is prime
example {F : Type*} [Field F] : ∀ p : Nat, Smallest (fun (n : Nat) => AddMonoid.nsmul n (1 : F) = (0 : F) ∧ n > 0) p → Prime p := by {
  intro p ⟨⟨hp1, hp1'⟩, hp2⟩
  rw [← Nat.irreducible_iff_prime]
  apply Irreducible.mk
  · cases em (p = 1) with
    | inl l =>
      simp only [l, nsmul_eq_smul, one_smul, one_ne_zero] at hp1
    | inr r =>
      simp [Nat.isUnit_iff, r]

  · intro a b h

    rw [h] at hp1
    simp only [nsmul_eq_smul, nsmul_eq_mul, Nat.cast_mul, mul_one, mul_eq_zero] at hp1

    wlog ha : (a : F) = 0 with IH
    · have := @IH F _ p hp1' hp2 b a (by linarith [h]) (by tauto) (by tauto)
      tauto
    · simp at hp2
      rw [h] at hp1'
      simp only [CanonicallyOrderedCommSemiring.mul_pos] at hp1'
      have ha' : a > 0 := hp1'.left
      have hb : b > 0 := hp1'.right
      specialize hp2 a ha ha'
      have : a ≤ a * b :=
        Nat.le_mul_of_pos_right hb
      rw [show p = a by linarith] at h
      exact Or.inr ∘ Nat.isUnit_iff.mpr <|
        (Nat.mul_right_eq_self_iff ha').mp (id h.symm)
}
end q5q6

section q7

open Complex

def conj (x : Complex):= (starRingEnd _) x

-- a)
example  (z : Complex) : (1 - 2 * I) * conj z = - I * (1 - I) ↔ z = ⟨(normSq (1 - I * 2))⁻¹, (normSq (1 - I * 2))⁻¹ * 3⟩   := by {
  apply Iff.intro
  intro h
  have : (1 - 2 * I) ≠ 0 := by simp [Complex.ext_iff]
  have w : conj z = (- I * (1 - I)) / (1 - 2 * I) :=
    CancelDenoms.cancel_factors_eq_div h this
  rw [Complex.ext_iff] at w
  rw [Complex.div_re, Complex.div_im] at w
  simp at w
  ring_nf at w
  rw [conj, Complex.conj_re, Complex.conj_im] at w
  have w1 : z.im = ((normSq (1 - I * 2))⁻¹ * 3) := by linarith [w.right]
  have : z = ⟨z.re, z.im⟩ := by exact rfl
  rw [w.left, w1] at this
  exact this

  intro h
  rw [h, Complex.ext_iff]
  apply And.intro

  simp [Complex.add_im, Complex.mul_im, Complex.mul_re, conj, Complex.conj_re, Complex.mul_re]
  simp [normSq]
  norm_num

  simp [Complex.add_im, Complex.mul_im, Complex.mul_re, conj, Complex.conj_re, Complex.mul_re]
  simp [normSq]
  norm_num
}

end q7
