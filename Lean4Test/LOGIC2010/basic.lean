import Mathlib.Lean.Expr.Basic


example (A B C : Prop) : (A → C) → (B → C) → A ∨ B → C := fun h1 h2 h => Or.elim h h1 h2

syntax "custom_tactic" term : tactic
macro_rules
| `(tactic| custom_tactic $e:term) => `(tactic| exact Eq.refl $e)

-- beta substitution
infixr :70 "/" => (fun (x : Prop → Prop) (y : Prop) => x y)

example : 10 + 10= 10 := by
  custom_tactic 10
