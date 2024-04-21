import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic

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

-- a) has solution
-- want ⟦5⟧ x = ⟦4⟧
-- 5 * 8 = 40 ≈ 4
example : ∃ (x : Quotient z12), (⟦5⟧ :  ℤ₁₂) * x + ⟦3⟧ = (⟦7⟧ : ℤ₁₂) := by
  use ⟦8⟧
  simp [mk_mul, mk_add]
  simp [HasEquiv.Equiv, Setoid.r]

-- b) has solution
-- we want 12 ∣ (3x + 6) = 3(x + 2)
-- so x + 2 is divisible by 4
-- that is x = -2
example : ∃ (x : Quotient z12), (⟦3⟧ :  ℤ₁₂) * x + ⟦11⟧ = (⟦5⟧ : ℤ₁₂) := by
  use ⟦-2⟧
  simp [mk_mul, mk_add]
  simp [HasEquiv.Equiv, Setoid.r]

-- c) has solution
-- -11 ≈ 1
-- we can use 5 since 5^2 = 25 ≈ 1
example : ∃ (x : Quotient z12), x * x  = -(⟦11⟧ : ℤ₁₂) := by
  use ⟦5⟧
  simp [Neg.neg, mk_mul]
  simp [HasEquiv.Equiv, Setoid.r]

end q4

section q5q6

def r (n : ℤ) (x y : ℤ) : Prop := n ∣ (x - y)

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
    apply Equivalence.mk
    · simp [r]
    · intro x y h; exact dvd_sub_comm.mp h

    intro x y z h1 h2
    have : n ∣ (x - y) + (y - z) :=
      Int.dvd_add h1 h2
    simp at this
    exact this
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

-- character of a ℤ[p]
example {p : Nat} : Smallest (fun (n : Nat) => AddMonoid.nsmul n (Quot.mk (r p) 1) = (0 : Quot (r p))) p := by
{
  apply And.intro
  simp only
  rw [nsmul_bruh p, zero_eq]
  rw [Quot.eq]
  rw [Equivalence.eqvGen_eq]
  simp [r]

  -- cringe stuff
  apply Equivalence.mk
  · simp [r]
  · intro x y h; exact dvd_sub_comm.mp h

  intro x y z h1 h2
  have : (p:ℤ) ∣ (x - y) + (y - z) :=
    Int.dvd_add h1 h2
  simp at this
  exact this
  -- cringe stuff

  intro b h
  apply by_contradiction
  simp
  intro h'
  rw [nsmul_bruh, zero_eq, Quot.eq, Equivalence.eqvGen_eq] at h
  simp [r] at h
  have : p ∣ b := by exact Int.ofNat_dvd.mp h
  match this with
  | ⟨k, hk⟩ => {
    have w : k > 0 := by sorry
    have : p = b / k :=by exact (Nat.div_eq_of_eq_mul_left w hk).symm
    have : b / k ≤ b := Nat.div_le_self b k
    linarith
  }
}
end q5q6
