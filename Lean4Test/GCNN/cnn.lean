import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open Matrix

def conv { R : Type u } [Ring R] {n : Nat} {k : Nat} (kernel : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) R) : Matrix (Fin (n + 2 * k)) (Fin (n + 2 * k)) R → Matrix (Fin n) (Fin n) R :=
fun m => of fun (x: Fin n) (y: Fin n) => ((List.finRange (2 * k + 1)).map <|
  fun i => ((List.finRange (2 * k  + 1)).map <|
    fun j => kernel (i - k) (j - k) * m ⟨x.val, by linarith [x.isLt]⟩ ⟨y.val, by linarith [y.isLt]⟩).sum).sum

theorem congr'' {α : Type u } {β : Type v} {γ : Type w} (f : α → β → γ) (α₁ α₂ : α) (b : β) : α₁ = α₂ → f α₁ b = f α₂ b := by tauto

-- translational equivariance of convolutions (up to padding)
theorem conv_equivariant { R : Type u } [Ring R] (n : Nat) (k : Nat) (kernel : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) R) (img : Matrix (Fin (n + 2 * k)) (Fin (n + 2 * k)) R) (i j : Fin n) : ∀ x' ≥ i, ∀ y' ≥ j, (of <| fun x y => (conv kernel img) (x - i) (y - j)) x' y' = conv kernel (of <| fun x y => img (x - ⟨i.val, by linarith [i.isLt]⟩) (y - ⟨j.val, by linarith [j.isLt]⟩)) x' y' := by
  intro x' hx' y' hy'
  rw [conv, conv, of_apply, of_apply]
  apply congrArg; apply congr''
  ext u
  apply congrArg; apply congr''
  ext v
  apply congrArg₂
  · rfl
  apply congrArg₂
  · rw [Fin.eq_iff_veq,]
    have : ({ val := ↑x', isLt := conv.proof_2 x' } : Fin (n + 2 * k)).val ≥ (⟨i.val, by linarith [i.isLt]⟩ : Fin (n + 2 * k)).val := by
      simp only [Fin.val_fin_le, hx']
    rw [Fin.coe_sub_iff_le.mpr this]
    exact Fin.coe_sub_iff_le.mpr hx'

  · rw [Fin.eq_iff_veq,]
    have : ({ val := ↑y', isLt := conv.proof_2 y' } : Fin (n + 2 * k)).val ≥ (⟨j.val, by linarith [j.isLt]⟩ : Fin (n + 2 * k)).val := by
      simp only [Fin.val_fin_le, hy']
    rw [Fin.coe_sub_iff_le.mpr this]
    exact Fin.coe_sub_iff_le.mpr hy'

def convCyCy { R : Type u } [Ring R] {n : Nat} {k : Nat} (kernel : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) R) : Matrix (Fin (n + 2 * k)) (Fin (n + 2 * k)) R → Matrix (Fin (n + 2 * k)) (Fin (n + 2 * k)) R :=
fun m => of <| fun x y => ((List.finRange (2 * k + 1)).map <|
  fun i => ((List.finRange (2 * k  + 1)).map <|
    fun j => kernel (i - k) (j - k) * m x y).sum).sum

theorem convCyCy_equivariant { R : Type u } [Ring R] (n : Nat) (k : Nat) (kernel : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) R) (img : Matrix (Fin (n + 2 * k)) (Fin (n + 2 * k)) R) (i j : Fin (n + 2 * k)) : (of <| fun x y => (convCyCy kernel img) (x - i) (y - j)) = convCyCy kernel (of <| fun x y => img (x - i) (y - j)) := by
  ext x' y'
  simp
  apply congrArg
  rfl

def convCy { R : Type u } [Ring R] {n : Nat} {k : Nat} (kernel : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) R) : Matrix (Fin (n + 2 * k)) (Fin (n + 2 * k)) R → Matrix (Fin n) (Fin (n + 2 * k)) R :=
fun m => of fun x φ => ((List.finRange (2 * k + 1)).map <|
  fun i => ((List.finRange (2 * k  + 1)).map <|
    fun j => kernel (i - k) (j - k) * m ⟨x.val, by linarith [x.isLt]⟩ φ).sum).sum

-- equivariance of cylindric convolution, up to padding for x-axis only and globally for y-axis
theorem convCyc_equivariant [Ring R] (n : Nat) (k : Nat) (kernel : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) R) (img : Matrix (Fin (n + 2 * k)) (Fin (n + 2 * k)) R) (i : Fin n) (j : Fin (n + 2 * k)) : ∀ x' ≤ i, (of <| fun x y => (convCy kernel img) (x - i) (y - j)) x' = (convCy kernel (of <| fun x y => img (x - ⟨i, by linarith [i.isLt]⟩) (y - j)) x') := by
  intro x' hx'
  ext y
  simp [convCy]
  apply congrArg; apply congr''
  ext u
  apply congrArg; apply congr''
  ext v
  apply congrArg; apply congrArg₂
  · rw [Fin.eq_iff_veq,]
    have : (⟨x', convCy.proof_2 x'⟩ : Fin (n + 2 * k)).val ≥ (⟨i, by linarith [i.isLt]⟩ : (Fin (n + 2 * k))).val  := by
      simp only [Fin.val_fin_le, hx']
    rw [Fin.coe_sub_iff_le.mpr this]
    simp
    exact Fin.coe_sub_iff_le.mpr this

  · rfl
