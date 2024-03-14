import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

-- sublist from index i inclusive to j exclusive
def List.slice (l : List ℝ) (i j : ℕ) : List ℝ := (l.drop i).take (j - i)

#check List.take
example : (l : List ℝ) → ∀ i : Fin l.length, l.slice i i = []
| [] => fun ⟨i, is⟩ => by simp at is
| a :: l => fun _ => by simp [List.slice]

example (l : List ℝ) (i : ℕ) : l.slice 0 i ++ l.slice i l.length = l := by
  simp [List.slice]
  have : (l.drop i).length = l.length - i := List.length_drop i l
  rw [← this]
  rw [List.take_length (List.drop i l)]
  exact List.take_append_drop i l

theorem slice_eq_take_take (b c : ℕ) (l : List ℝ) (hbc : b ≤ c) : l.slice 0 b = (l.take c).take b := by
{
  simp [List.slice]
  have : b < c + 1 := by linarith
  refine (List.ext ?_).symm
  intro n
  by_cases h : n < b
  {
    have : n < c:= by linarith
    rw [List.get?_take h, List.get?_take h, List.get?_take this]
  }
  {
    simp at h

    have : (List.take b (List.take c l)).length ≤ b := List.length_take_le b (List.take c l)
    have : (l.take b).get? n = none := List.get?_len_le (by linarith [List.length_take_le b l])
    rw [this]
    by_cases h1 : n < c
    {
      have : (List.take b (List.take c l)).length ≤ n := by linarith
      exact List.get?_len_le this
    }
    {
      simp at h1
      exact List.get?_len_le (by linarith)
    }
  }
}

#check List.length_drop
#check List.get?_take
theorem slice_eq_take_drop (b c : ℕ) (l : List ℝ) (hbc : b ≤ c) : l.slice b c = (l.take c).drop b := by
{
  simp [List.slice]
  have : b < c + 1 := by linarith
  refine (List.ext ?_).symm
  intro n
  by_cases h : b + n < c
  {
    simp [List.get?_drop, List.get?_take h]
    have : n < c - b := by exact lt_tsub_iff_left.mpr h
    rw [List.get?_take this, List.get?_drop]
  }
  {
    simp at h
    have : (l.take c).length ≤ c := List.length_take_le c l
    have : b + n ≥ (l.take c).length := by linarith
    rw [List.get?_drop, List.get?_len_le this]

    have : n ≥ c - b := by exact Nat.sub_le_iff_le_add'.mpr h
    have : (List.take (c - b) (List.drop b l)).length ≤ c - b := List.length_take_le (c-b) _
    have : List.length (List.take (c - b) (List.drop b l)) ≤ n := by linarith
    rw [List.get?_len_le this]
  }
}
example (b c : ℕ) (l : List ℝ) (hbc : b ≤ c) : l.slice 0 c = l.slice 0 b ++ l.slice b c := by
{
  rw [slice_eq_take_drop b c l hbc, slice_eq_take_take b c l hbc]
  simp only [List.slice, tsub_zero, List.drop_zero, List.take_append_drop]
}

def isGreaterThan0 (x : Nat) : IO Bool := do
  IO.println s!"value: {x}"
  return x > 0

def f (x : Nat) : IO Unit := do
  let c ← isGreaterThan0 x
  if c then
    IO.println s!"{x} is greater than 0"
  else
    pure ()
  for i in List.range 10 do
     IO.println s!"wow"
  #check Id.run

#print f


-- always even loop invariant
def f' (x : Nat) : IO (Subtype (fun x => ∃ k, x = 2*k)) :=
  forIn (List.range 10) (⟨2, by {use 1}⟩ : Subtype (fun x => ∃ k, x = 2*k)) fun i r => do
    pure (ForInStep.yield ⟨2*r, by {use r}⟩)

#print f'

#check Tree
