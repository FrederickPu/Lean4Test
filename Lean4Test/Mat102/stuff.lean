import Mathlib.RingTheory.Bezout

#check Int.instDvdInt
#check Mod
#check Int.instModInt
example (a b : ℤ) : ((a*b : ℤ) : Fin 5) = (a : Fin 5) * (b : Fin 5) := by exact Int.cast_mul a b
example (a b : ℕ) : (a*b)%5 = ((a%5)*(b%5))%5:= by library_search

example (a : ℤ) : ((5*a : ℤ) : Fin 5) = 0 := by {
  rw [Int.cast_mul]
  have : (5 : Fin 5) = 0 := rfl
  simp [this]
}

#check Int.mod_lt_of_pos
#check Int.mod_nonneg_of_pos
#check Int.si
def bruv (a : ℤ) : ((a : Fin 5):ℤ)  = (a % 5 : ℤ) := by {
  rw [← Int.emod_add_ediv a 5]
  rw [Int.cast_add, Int.cast_mul]
  rw [Int.add_emod, Int.mul_emod]
  simp
  have : (5 : Fin 5) = 0 := rfl
  rw [this]
  simp

  suffices : a % 5 < 5
  have : a % 5 = Int.toNat (a % 5) := (Int.toNat_of_nonneg l).symm
  rw [this]
  rw [Int.cast_ofNat, Fin.coe_ofNat_eq_mod, Int.ofNat_emod, Nat.cast_ofNat]
  rw [← this]
  exact Int.emod_emod a 5

  exact Int.emod_lt_of_pos a (by linarith)
}
#check Int.emod_lt_of_pos
#check Int.emod_nonneg
#check Fin.mul_zero
#check mul_eq_zero

example (a b : Fin 5) : a = 0 ∨ b = 0 → a*b = 0 := by library_search

def wow : (n : ℕ) → 5 ∣ ((n:ℤ)^5  - n)
| 0 => by decide
| (n + 1) => by {
  push_cast
  ring_nf
  have : (n:Fin 5) * 4 + ↑n ^ 2 * 10 + ↑n ^ 3 * 10 + ↑n ^ 4 * 5 + (↑n ^ 5 - n) =
}
example (a : ℤ) : (a : Fin 5) = 0 → 5 ∣ a := by
  intro h
  have : ((a : Fin 5) : ℤ) = 0 := by rw [h]; simp
  rw [bruv a] at this
  exact Int.modEq_zero_iff_dvd.mp this
example (a : ℤ) :  5 ∣ a → (a : Fin 5) = 0 := by
  intro ⟨k, h⟩
  rw [h]
  have : (5 : Fin 5) = 0 := rfl
  push_cast
  rw [this]
  exact zero_mul _

example (x : ℤ) : 5 ∣ (x^5 - x):= by
{
  suffices : (x^5 - x) % 5 = 0
  exact Int.modEq_zero_iff_dvd.mp this

  suffices : ((x^5 - x : ℤ) : Fin 5) = (0: Fin 5)
  rw [← bruv]
  rw [this]
  rfl

  have : ((x^2 + 1 : ℤ) : Fin 5) = (((x + 2)*(x - 2):ℤ) : Fin 5) := by {
    ring
    have : -(4:Fin 5) = 1 := rfl
    push_cast
    rw [this]
  }
  have : ((x ^ 5 - x:ℤ): Fin 5) = (((x - 2)*(x - 1)*x*(x+1)*(x+2):ℤ):Fin 5) := calc
     ((x ^ 5 - x:ℤ): Fin 5)  =  ((x*(x^2 + 1)*(x+1)*(x - 1):ℤ): Fin 5) := by ring_nf
     ((x*(x^2 + 1)*(x+1)*(x - 1):ℤ): Fin 5)  = ((x^2 + 1:ℤ) : Fin 5) * ((x*(x+1)*(x - 1):ℤ): Fin 5) := by push_cast; ring
     ((x^2 + 1:ℤ) : Fin 5) * ((x*(x+1)*(x - 1):ℤ): Fin 5) =  (((x+2)*(x-2):ℤ) : Fin 5) * ((x*(x+1)*(x - 1):ℤ): Fin 5) := by rw [this]
     (((x+2)*(x-2):ℤ) : Fin 5) * ((x*(x+1)*(x - 1):ℤ): Fin 5) = (((x - 2)*(x-1)*x*(x+1)*(x+2) : ℤ) : Fin 5) := by push_cast; ring
  rw [this]

}
