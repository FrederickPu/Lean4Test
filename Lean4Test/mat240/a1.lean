import Mathlib.Algebra.Field.Defs
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic

/-
A1 of MAT240

non-verbose: designed to have as concise and readible proofs as possible.
Uses as little redundant mathlib theorems as possible
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

-- we don't use quotients like in a1-verbose
-- instead we just `[ZMOD 12]` to encode the same ideas

theorem equiv_sub {p a b c : ℤ} (h : b ≡ c [ZMOD p] ) : b ≡ a [ZMOD p] ↔ c ≡ a [ZMOD p] := by
  apply Iff.intro
  exact fun a_1 => Int.ModEq.trans (id (Int.ModEq.symm h)) a_1
  exact fun a_1 => Int.ModEq.trans h a_1

-- proof for q4 c)
example (x : ℤ) : x^2 ≡ -11 [ZMOD 12] ↔ x ≡ 1 [ZMOD 12] ∨ x ≡ 5 [ZMOD 12] ∨ x ≡ 7 [ZMOD 12] ∨ x ≡ 11 [ZMOD 12]:= by
  have temp {a : ℤ} (hx : x ≡ a [ZMOD 12]) : x^2 ≡ a^2 [ZMOD 12] := Int.ModEq.pow 2 hx
  mod_cases x % 12
  all_goals
  · simp [equiv_sub (temp H), equiv_sub H]

-- proof for q4 a)
example (x : ℤ) : 5 * x + 3 ≡ 7 [ZMOD 12] ↔ x ≡ 8 [ZMOD 12] := by
  have temp {a : ℤ} (hx : x ≡ a [ZMOD 12]) : 5 * x + 3 ≡ 5 * a + 3 [ZMOD 12] := by
    have : 5 * x ≡ 5 * a [ZMOD 12] :=
      Int.ModEq.mul rfl hx
    exact Int.ModEq.add this rfl
  mod_cases x % 12
  all_goals
  · simp only [equiv_sub <| temp H, equiv_sub H]

-- proof for q4 b)
example (x : ℤ) : 3 * x + 11 ≡ 5 [ZMOD 12] ↔ x ≡ 2 [ZMOD 12]  ∨ x ≡ 6 [ZMOD 12] ∨ x ≡ 10 [ZMOD 12] := by
  have temp {a : ℤ} (hx : x ≡ a [ZMOD 12]) : 3*x + 11 ≡ 3*a + 11 [ZMOD 12] := by
    have : 3 * x ≡ 3 * a [ZMOD 12] :=
      Int.ModEq.mul rfl hx
    exact Int.ModEq.add this rfl
  mod_cases x % 12
  all_goals
  · simp only [equiv_sub <| temp H, equiv_sub H]

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

instance instQrAdd {n : ℤ} : Add (Quot (r n)) := {
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

instance instQrMul {n : ℤ} : Mul (Quot (r n))  := {
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


instance instQrZero {n : ℤ} : Zero (Quot (r n)) :=
  ⟨Quot.mk _ 0⟩
instance instQrOne {n : ℤ} : One (Quot (r n)) :=
  ⟨Quot.mk _ 1⟩

theorem zero_eq : (0 : Quot (r n)) = Quot.mk _ 0 := by rfl
theorem one_eq {n : ℤ} : (1 : Quot (r n)) = Quot.mk _ 1 := by rfl

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

-- q5 a) proof
-- proved condition for multiplicative inverses
theorem q5_a (n : ℤ) (x : ℤ) : Int.gcd n x = 1 ↔ ∃ x' : (Quot (r n)), (Quot.mk _ x : Quot (r n)) * x' = Quot.mk _ 1 := by
  apply Iff.intro
  intro h
  match Int.gcd_eq_sum n x with
  | ⟨a, b, hab⟩ =>
    simp [h] at hab
    use Quot.mk _ b
    rw [mk_mul, Quot.eq]
    exact EqvGen.rel (x * b) 1 <|
      Dvd.intro_left (-a) (by linarith)

  intro ⟨x', hx'⟩
  match x'.exists_rep with
  | ⟨x'', hx''⟩ =>
    rw [← hx'', mk_mul, Quot.eq, Equivalence.eqvGen_eq lmao, r] at hx'

    match hx' with
    | ⟨k, hk⟩ =>
      have w := Int.gcd_le_sum n x (-k) x''
      rw [show (-k) * n + x'' * x = 1 by linarith] at w
      simp at w
      cases em (x = 0) with
      | inl l =>
        simp [l] at hx'
        simp [l]
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

def Smallest {α : Type*} [LE α] (p : α → Prop) (a : α) := p a ∧ ∀ b, p b → a ≤ b

-- a * x + b * y = 1

-- Any field formed on Z_p with canonical multiplication, zero and one must be of prime order
-- note that we only need the fact that mul is canonical since it restricts the possibilities for add.
theorem q5_b_mp {p : Nat} (hp : p > 1) : (∃ inst : (Field (Quot (r p))), inst.mul = instQrMul.mul ∧ inst.one = instQrOne.one ∧ inst.zero = instQrZero.zero) → Prime p := by {
    -- hCM : inst has canonical multiplication on Z_p
    -- hCO : inst has canonical multiplicative identity on Z_p
    intro ⟨inst, hCM, hCO, hCZ⟩
    have := inst.mul_inv_cancel
    rw [← Nat.irreducible_iff_prime]
    apply Irreducible.mk
    · rw [Nat.isUnit_iff]
      linarith

    intro a b H
    cases em (Quot.mk (r p) a = inst.zero) with
    | inl l => {
      -- the Zero for `inst` is the same as the zero used in `q5_a`
      simp [OfNat.ofNat, hCZ] at l
      rw [show instQrZero.zero = Quot.mk _ 0 by rfl] at l
      rw [Quot.eq, Equivalence.eqvGen_eq lmao, r] at l
      ring_nf at l
      rw [Int.ofNat_dvd] at l
      match l with
      | ⟨k, hk⟩ => { -- show that a = p
        have hab : a * b > 0 := by linarith
        have : a > 0 := by
          rw [mul_comm] at hab
          exact lt_of_nsmul_lt_nsmul b hab
        rw [hk] at this

        have : k > 0 :=
          lt_of_nsmul_lt_nsmul p this
        have : p ≤ p * k :=
          Nat.le_mul_of_pos_right this
        have : p > 0 := by linarith
        rw [H] at this

        have : b > 0 :=
          lt_of_nsmul_lt_nsmul a this
        have : a ≤ a * b :=
          Nat.le_mul_of_pos_right this

        simp [show a = p  by linarith] at H
        have := Eq.symm H
        rw [Nat.mul_right_eq_self_iff (by linarith)] at this
        exact Or.inr -- b = 1
          <| Nat.isUnit_iff.mpr this
    }
    }
    | inr r => { -- show that a = 1
      specialize this _ r
      have : Int.gcd ↑p ↑a = 1 := by
        rw [q5_a p a]
        use (Quot.mk _ a)⁻¹
        simp only [HMul.hMul, ← hCM]
        rw [← one_eq]
        simp [OfNat.ofNat, ← hCO]
        exact this
      have : Nat.gcd a p = 1 := Nat.coprime_comm.mpr this
      rw [← Nat.coprime_iff_gcd_eq_one] at this
      apply Or.inl -- a = 1
      rw [Nat.isUnit_iff]
      exact Nat.Coprime.eq_one_of_dvd this ⟨b, H⟩
    }
}

-- for any prime number p, Z_p with canonical add, mul, zero, one can be made into a field with the right choice of ⁻¹
theorem q_5_b_mpr {p : Nat} (hp : p > 1) : Prime p → (∃ inst : (Field (Quot (r p))), inst.mul = instQrMul.mul ∧ inst.one = instQrOne.one ∧ inst.zero = instQrZero.zero) := by
  intro H
  have : ∀ x, ∃ x' : (Quot (r p)), ¬ p ∣ x.natAbs → (Quot.mk _ x : Quot (r p)) * x' = Quot.mk _ 1 := by
    intro x
    cases em (p ∣ x.natAbs) with
    | inl l =>
      simp only [l, IsEmpty.forall_iff, exists_const]
    | inr r =>
      simp [r]
      rw [← q5_a, show Int.gcd p x = Nat.gcd p (x.natAbs) by rfl,
      ← Nat.Coprime, Nat.Prime.coprime_iff_not_dvd (Nat.prime_iff.mpr H)]
      exact r
  rw [Classical.skolem] at this
  have w : ∀ x : Quot (r p), ∃ x', (Quot.mk _ x') = x := by
    intro x
    exact Quot.exists_rep x
  rw [Classical.skolem] at w
  match this, w with
  | ⟨f, hf⟩, ⟨g, hg⟩ =>
    -- the conacaleness proofs are proved by rfl cause the type class system already inherits the predefined notions of one, zero etc.
    use {
      mul_comm := by
        intro a b
        match a.exists_rep, b.exists_rep with
        | ⟨a', ha'⟩, ⟨b', hb'⟩ =>
          rw [← ha', ← hb']
          simp [mk_mul]
          ring
      inv := fun x => if p ∣ (g x).natAbs then 0 else (f ∘ g) x
      exists_pair_ne := by
        use Quot.mk _ 0
        use Quot.mk _ 1
        simp [Quot.eq, Equivalence.eqvGen_eq lmao, r, Int.ofNat_dvd_left]
        linarith
      mul_inv_cancel := by
        intro a ha
        specialize hg a
        specialize hf (g a)
        rw [hg] at hf
        simp [Inv.inv]
        have : Quot.mk (r p) (g a) ≠ Quot.mk _ 0 := by
          rw [← hg, zero_eq] at ha
          exact ha
        simp [Quot.eq] at this
        rw [Equivalence.eqvGen_eq lmao, r, Int.ofNat_dvd_left] at this
        simp at this
        rw [if_neg this]
        exact hf this
      inv_zero := by {
        simp only [Inv.inv, Nat.isUnit_iff, Function.comp_apply, ite_eq_left_iff, OfNat.ofNat, Zero.zero]
        simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero, Nat.isUnit_iff]

        intro h
        specialize hg 0
        rw [zero_eq] at hg
        simp [Quot.eq] at hg
        rw [Equivalence.eqvGen_eq lmao, r] at hg
        simp [Int.ofNat_dvd_left] at hg
        apply False.elim
        exact h hg
      }
    }

-- Q5 b) a ℤ_p is a field with canonical mul, one, zero iff p is prime
theorem q5_b_full {p : Nat} (hp : p > 1) : (∃ inst : (Field (Quot (r p))), inst.mul = instQrMul.mul ∧ inst.one = instQrOne.one ∧ inst.zero = instQrZero.zero) ↔ Prime p :=
  Iff.intro (fun a => q5_b_mp hp a) (fun a => q_5_b_mpr hp a)

theorem nsmul_bruh {p : Nat} (n : Nat) : AddMonoid.nsmul n (Quot.mk (r p) 1) = Quot.mk (r p) n := by
  induction n with
  | zero =>
    rw [AddMonoid.nsmul_zero]
    simp [zero_eq]
  | succ n ih =>
    rw [AddMonoid.nsmul_succ]
    rw [ih, mk_add]
    simp
    ring_nf

-- Q6 a) character of a ℤ[p]
-- Note would be better to use `charP` to make it more inline with mathlib4
example {p : Nat} (hp : p > 0) : Smallest (fun (n : Nat) => AddMonoid.nsmul n (Quot.mk (r p) 1) = (0 : Quot (r p)) ∧ n > 0) p := by
  apply And.intro
  · simp only
    rw [nsmul_bruh p, zero_eq, Quot.eq, Equivalence.eqvGen_eq lmao]
    simp [r]
    exact hp

  intro b h
  apply by_contradiction
  · intro h'
    rw [nsmul_bruh, zero_eq, Quot.eq, Equivalence.eqvGen_eq lmao] at h
    simp [r] at h
    have : p ∣ b := by exact Int.ofNat_dvd.mp h.1
    match this with
    | ⟨k, hk⟩ =>
      have w : k > 0 := by
        apply by_contradiction
        simp
        intro hw
        simp [hw] at hk
        linarith
      have : p = b / k := by exact (Nat.div_eq_of_eq_mul_left w hk).symm
      have : b / k ≤ b := Nat.div_le_self b k
      linarith

-- Q6 b) if a field has a non-zero characteristic, it is prime
example {F : Type*} [Field F] : ∀ p : Nat, Smallest (fun (n : Nat) => AddMonoid.nsmul n (1 : F) = (0 : F) ∧ n > 0) p → Prime p := by
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

end q5q6

section q7

open Complex

def conj (x : Complex):= (starRingEnd _) x

-- a)
example  (z : Complex) : (1 - 2 * I) * conj z = - I * (1 - I) ↔ z = ⟨(normSq (1 - I * 2))⁻¹, (normSq (1 - I * 2))⁻¹ * 3⟩ := by
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

end q7

section q8

#check Fin.instCommRing

theorem Fin.natCast_eq_zero{a : ℕ} {n : ℕ} [NeZero n] :
  (a:Fin n) = 0 ↔ n ∣ a := by sorry

def primeinstNoZeroDivisors {p : Nat} [NeZero p] (hp2 : Nat.Prime p) : NoZeroDivisors (Fin p) := ⟨
  by
  intro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have : { val := a, isLt := ha } = (a : Fin p) := by
    apply Fin.eq_of_veq
    exact (Nat.mod_eq_of_lt ha).symm
  rw [this] at hab
  rw [this]
  have : { val := b, isLt := hb } = (b : Fin p) := by
    apply Fin.eq_of_veq
    exact (Nat.mod_eq_of_lt hb).symm
  rw [this] at hab
  rw [this, Fin.natCast_eq_zero, Fin.natCast_eq_zero]
  rw [← Nat.cast_mul, Fin.natCast_eq_zero] at hab
  exact (Nat.Prime.dvd_mul hp2).mp hab
⟩

-- Polynomial.coeff
#check Polynomial.degree_lt_iff_coeff_zero
theorem Polynomial.degree_eq_one_iff (p : Polynomial (Fin 5)) : p.degree = 1 ↔ ∃ a b, a ≠ 0 ∧ p = (Polynomial.C a)  * Polynomial.X + (Polynomial.C b) := by {
  apply Iff.intro
  intro h
  have : Polynomial.degree p < (2: ℕ) := by
    rw [h]
    simp only
  rw [Polynomial.degree_lt_iff_coeff_zero] at this
  use Polynomial.coeff p 1
  use Polynomial.coeff p 0
  apply And.intro
  · intro h'
    have : p = Polynomial.C (Polynomial.coeff p 0) := by
      rw [← Polynomial.coeff_inj]
      ext m
      match m with
      | 0 => simp
      | 1 => simp [h']
      | Nat.succ (Nat.succ m) =>
        specialize this m.succ.succ (by linarith)
        simp [this]
    rw [this, Polynomial.degree_C] at h
    simp at h

    intro H
    · rw [H] at h
      simp at h
  · rw [← Polynomial.coeff_inj]
    ext m
    match m with
    | 0 => simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero,
        Polynomial.coeff_X_zero, mul_zero, zero_add]
    | 1 => simp only [Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_C_zero,
      Polynomial.coeff_C_succ, add_zero]
    | Nat.succ (Nat.succ m) => {
      specialize this m.succ.succ (by {
        linarith
      })
      simp [this]
    }

  · intro ⟨a, b, ha, H⟩
    rw [H]

    have := primeinstNoZeroDivisors <| (Nat.prime_iff_card_units 5).mpr rfl

    rw [Polynomial.degree_add_C, Polynomial.degree_C_mul ha, Polynomial.degree_X]
    rw [Polynomial.degree_C_mul ha, Polynomial.degree_X]
    simp only
}

theorem Polynomial.irreducible_iff_degree_lt{R : Type u} [Field R] (p : Polynomial R) (hp0 : p ≠ 0) (hpu : ¬IsUnit p) :
Irreducible p ↔ ∀ (q : Polynomial R), Polynomial.degree q ≤ (Polynomial.natDegree p / 2 : ℕ) → q ∣ p → IsUnit q := sorry


instance : Field (Fin 5) := {
  inv :=
  fun x => match x with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 4
  | ⟨x + 5, isLt⟩ => by linarith
  mul_inv_cancel := by simp only
  inv_zero := by simp only
  div_eq_mul_inv := by sorry
}

theorem Polynomial.not_isUnit_of_degree_pos{R : Type u} [Semiring R] [NoZeroDivisors R] (p : Polynomial R) (hpl : 0 < Polynomial.degree p) :
¬IsUnit p := sorry

-- note: Units in polynomial rings are the constant polynomials
-- so x^2 + 1 and 3 x^2 + 3 are both considered irreducible even though 3 x^2 + 3 has a common factor 3
theorem Polynomial.eq_degree1_mul_degree1_of_reducible_degree2 (p : Polynomial (Fin 5)) (hp : Polynomial.degree p = 2) (hp2 : ¬ Irreducible p) : ∃ p1 p2, p1.degree = 1 ∧ p2.degree = 1 ∧ p = p1 * p2 := by {
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hpu : ¬ IsUnit p := by
    apply Polynomial.not_isUnit_of_degree_pos
    simp [hp]
  rw [Polynomial.irreducible_iff_degree_lt _ hp0 hpu] at hp2
  simp at hp2
  match hp2 with
  | ⟨p1, ⟨p2, hp12⟩, hp1', H⟩ => {
    have crux : Polynomial.natDegree p = 2 :=
      Polynomial.natDegree_eq_of_degree_eq_some hp
    simp [crux] at hp1'
    suffices Polynomial.degree p1 = 1 by
      have w : Polynomial.degree (p1 * p2) = Polynomial.degree p1 + Polynomial.degree p2 :=
        Polynomial.degree_mul
      rw [← hp12] at w
      rw [w, this] at hp
      have : (1 : ℕ) + p2.degree = (1 + 1 : ℕ) := hp
      simp at this
      have := WithBot.add_left_cancel (by simp only) this
      use p1
      use p2
    match h : p1.degree with
    | none => {
      rw [show none = (⊥ : WithBot ℕ) from rfl] at h
      rw [Polynomial.degree_eq_bot] at h
      simp [h] at hp12
      simp [hp12] at hp
    }
    | some 0 =>
      apply Polynomial.eq_C_of_degree_eq_zero at h
      rw [Polynomial.isUnit_iff] at H
      apply False.elim ∘ H
      use Polynomial.coeff p1 0
      simp only [h.symm, and_true]
      suffices p1.coeff 0 ≠ 0 by {
        use ⟨p1.coeff 0, (p1.coeff 0)⁻¹, by {
          rw [mul_inv_cancel]
          intro h
          simp [h] at this
        }, by {
          rw [inv_mul_cancel]
          intro h
          simp [h] at this
        }⟩
      }
      intro h'
      rw [h'] at h
      simp [h] at hp12
      simp [hp12] at hp

    | some 1 => rfl
    | some (x + 2) =>
      rw [h] at hp1'
      have : (1 :WithBot ℕ) = (some 1 : WithBot ℕ) := by rfl
      rw [this] at hp1'
      have : Nat.succ (Nat.succ x) ≤ 1 := by exact WithBot.coe_le_one.mp hp1'
      linarith
  }
}

end q8
