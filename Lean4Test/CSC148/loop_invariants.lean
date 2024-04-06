import Mathlib.Tactic

-- always even loop invariant
def f' (x : Nat) : IO (Subtype (fun x => ∃ k, x = 2*k)) :=
  forIn (List.range 10) (⟨2, by {use 1}⟩ : Subtype (fun x => ∃ k, x = 2*k)) fun i r => do
    pure (ForInStep.yield ⟨2*r, by {use r}⟩)
