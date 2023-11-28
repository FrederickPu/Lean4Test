import Mathlib.Tactic
import Mathlib.Data.List.Card

-- and, or, not
inductive LogicTree
| var (name : Nat) : LogicTree
| and : LogicTree → LogicTree → LogicTree
| or : LogicTree → LogicTree → LogicTree
| not : LogicTree → LogicTree

def LogicTree.var_lookup := ["P", "Q", "R", "S", "T", "U", "V"]
def LogicTree.toString : LogicTree → String
| var name => if h : name < LogicTree.var_lookup.length then LogicTree.var_lookup.get ⟨name, h⟩ else name.repr
| and left right => "(" ++ left.toString ++ "∧" ++ right.toString ++ ")"
| or left right => "(" ++ left.toString ++ "∨" ++ right.toString ++ ")"
| not x => "(" ++ "¬" ++ x.toString ++ ")"

#check List.append
def dnf_add : List (List (Bool × Nat)) → List (List (Bool × Nat)) → List (List (Bool × Nat))
| c :: l, r => (r.map (fun x => (x ++ c))) ++ (dnf_add l r)
| [], _ => []
def dnf_sum : List (List (List (Bool × Nat))) → List (List (Bool × Nat))
| C :: L => dnf_add C (dnf_sum L)
| [] => [[]]

def var_toString : Bool × Nat → String
| ⟨flag, name⟩ => (if flag then "" else "¬") ++ (if h : name < LogicTree.var_lookup.length then LogicTree.var_lookup.get ⟨name, h⟩ else name.repr)
def dis_toString : List (Bool × Nat) → String
| v1 :: v2 :: l => var_toString v1 ++ "∨" ++ (dis_toString (v2 :: l))
| v :: [] => var_toString v
| [] => ""

def dnf_toString : List (List (Bool × Nat)) → String
| conj1 :: conj2 :: L => "(" ++ dis_toString conj1 ++ ")" ++ " ∧ " ++ (dnf_toString (conj2 :: L))
| conj2 :: [] => "(" ++ dis_toString conj2 ++ ")"
| [] => ""
#check true
#eval dnf_sum [[[(true, 1)], [(true, 2)]], [[(true, 2)], [(true, 3)]], [[(true, 4)], [(true, 5)]]]
#eval dnf_toString <| dnf_prod [[[(false, 1)], [(true, 2)]], [[(true, 2)], [(true, 3)]], [[(true, 4)], [(true, 5)]]]

-- convert logical tree to disjunctive normal form
def LogicTree.dnf : LogicTree → List (List (Bool × Nat))
| var name => [[(true, name)]]
| or left right => dnf_add left.dnf right.dnf
| and left right => left.dnf ++ right.dnf
| not x => dnf_sum (x.dnf.map (fun y => y.map (fun u => [(!u.1, u.2)])))

#eval (LogicTree.and (LogicTree.or (LogicTree.var 1) (LogicTree.var 2))  (LogicTree.or (LogicTree.var 3) (LogicTree.var 4))).toString
#eval dnf_toString (LogicTree.not <| LogicTree.and (LogicTree.or (LogicTree.var 1) (LogicTree.var 2))  (LogicTree.or (LogicTree.var 3) (LogicTree.var 4))).dnf

example (Q R S T : Prop) : ¬ ((Q ∨ R) ∧ (S ∨ T)) ↔ ((¬T∨¬R) ∧ (¬S∨¬R) ∧ (¬T∨¬Q) ∧ (¬S∨¬Q)) := by
tauto

#check List.contains
#check List.find
def resolve (l1 l2 : List (Bool × Nat)) : Option (List (Bool × Nat)) := Id.run do
  for item in l1 do
    if l2.contains ⟨!item.fst, item.snd⟩ then return (l1.remove item) ++ l2.remove ⟨!item.fst, item.snd⟩
  return none

instance : ToString LogicTree :=
{
  toString := fun lt => if
}
