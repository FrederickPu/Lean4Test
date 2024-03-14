import Mathlib.Data.Real.Basic

namespace q4

variable {α : Type} (A B : Set α)
example : A ∪ B = A → B ⊆ A := by
  intro h
  exact Set.union_eq_left.mp h

example : A \ B = A → A ∩ B = ∅ := by
  intro h
  have : (A ∩ Bᶜ) ∩ B = A ∩ B := by exact congrFun (congrArg Inter.inter h) B
  rw [Set.inter_assoc, Set.compl_inter_self, Set.inter_empty] at this
  exact this.symm

example : A ∩ B = A → A ⊆ B := by
  intro h
  exact Set.inter_eq_left.mp h

theorem help_iv : A \ B = B \ A → B ⊆ A := by
  intro h
  have w : (A \ B) ∩ B = (B \ A) ∩ B := (Subtype.preimage_val_eq_preimage_val_iff B (A \ B) (B \ A)).mp
      (congrArg (Set.preimage Subtype.val) h)
  simp at w
  have : (B \ A) ∩ B = B \ A := by
    simp only [Set.inter_eq_left]
    exact Set.diff_subset B A
  rw [this] at w
  exact Set.diff_eq_empty.mp (id w.symm)

example :  A \ B = B \ A → A = B := by
  intro h
  apply Set.Subset.antisymm
  exact help_iv B A h.symm
  exact help_iv A B h

end q4

namespace q5

variable {α : Type} (A B C D : Set α) (h1 : A ⊆ C) (h2 : B ⊆ D)

example : A ∪ B ⊆ C ∪ D := by
  intro x hx
  cases hx with
  | inl l =>
    left
    exact h1 l
  | inr r =>
    right
    exact h2 r

example : A ∩ B ⊆ C ∩ D := by
  intro x hx
  apply And.intro
  exact h1 hx.left
  exact h2 hx.right

end q5

namespace q6q7

variable {α : Type} (A B : Set α)

example : A ⊆ B → A ⊆ Bᶜ → A = ∅ := by
  intro h1 h2
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x hx
  specialize h1 hx
  specialize h2 hx
  exact h2 h1

#check Set.eq
example : A ⊆ B → Aᶜ ⊆ B → B = Set.univ := by
  intro h1 h2
  rw [Set.eq_univ_iff_forall]
  intro x
  cases em (x ∈ A) with
  | inl l => exact h1 l
  | inr r => exact h2 r

end q6q7

namespace q8

example : Decidable <| {α : Type} → (A B C : Set α) → (A \ (A ∩ B)) ∩ B = A ∩ B := by
  apply Decidable.isFalse
  simp

  use ℕ
  use {0}
  use {0}
  intro h
  simp only [Set.inter_self] at h
  have h := h.symm
  rw [Set.eq_empty_iff_forall_not_mem] at h
  specialize h 0
  simp only at h

example {α : Type} (A B C : Set α) : (A ∪ B)ᶜ ∩ C = Aᶜ ∩ Bᶜ ∩ C := by
  simp only [Set.compl_union]

inductive bruh
| a : bruh
| b : bruh
| c : bruh
| d : bruh

example : Decidable <| {α : Type} → (A B C : Set α) → (A ∩ B)ᶜ ∩ Cᶜ = (A ∩ B ∩ C)ᶜ := by
{
  apply isFalse
  simp
  use bruh
  use {bruh.a, bruh.b}
  use {bruh.b, bruh.c}
  use {bruh.c, bruh.d}

  intro h
  have : {bruh.a, bruh.b} ∩ {bruh.b, bruh.c} = ({bruh.b} : Set bruh) := by {
    ext x
    cases x
    all_goals {
      rw [Set.mem_inter_iff]
      simp only [Set.mem_singleton_iff, Set.mem_insert_iff]
    }
  }
  rw [this] at h
}

end q8


example (A B : Prop) : (A ∨ B) ∧ (A ∨ ¬ B) ∨ (¬ A ∨ B) ∧ (¬ A ∨ ¬ B) ↔ True := by tauto

example (A B : Prop) : ((A ∨ B) ∨ C) ∧ (A ∨ B ∨ ¬ C) ∧ (A ∨ ¬ B) ↔ A := by tauto

example (A B C : Prop) : A ∨ B ∨ C ↔ A ∨ ¬ A ∧ B ∨ ¬ A ∧ ¬ B ∧ C := by tauto


example (A B C : Set ℝ) : (A \ B) \ C = (A \ C) \ (B \ C) := by {
  simp only [Set.diff_eq_compl_inter]
  rw [Set.compl_inter]
  rw [compl_compl]
  rw [Set.inter_distrib_right]
  rw [← Set.inter_assoc C (Cᶜ)]
  simp only [Set.inter_compl_self, Set.empty_inter, Set.empty_union]
  rw [← Set.inter_assoc, Set.inter_comm Cᶜ (Bᶜ)]
  rw [Set.inter_assoc]
}


-- tree of depth n
inductive Tree
| nil : Tree
| root : Nat → Tree
| cons : Tree → Tree → Tree

def Tree.subtrees : Tree → List Tree
| Tree.nil => []
| Tree.root _ => []
| Tree.cons t T => t :: T.subtrees

def Tree.init : Nat → List Tree → Tree
| n, [] => Tree.root n
| n, a :: l => Tree.cons a (Tree.init n l)

def Tree.depth : Tree → Nat
| Tree.nil => 0
| Tree.root _ => 1
| Tree.cons t T => max (t.depth + 1) T.depth

def List.wrap {α : Type} : (l : List α) → List (Subtype (fun x : α => x ∈ l))
| [] => []
| a :: l =>
  Id.run do
    let temp : List (Subtype (fun x => x ∈ a :: l)):= l.wrap.map (fun ⟨x, hx⟩ => ⟨x, mem_cons_of_mem a hx⟩)
    return ⟨a, mem_cons_self a l⟩ :: temp

def Tree.set_root : Tree → Nat → Tree
| Tree.nil, _ => Tree.nil
| Tree.root n, _root => Tree.root _root
| Tree.cons t T, _root => Tree.cons t (T.set_root _root)

def Tree.get_root : Tree → Option Nat
| Tree.nil => none
| Tree.root n => some n
| Tree.cons _ T => T.get_root

theorem List.wrap_canc {α : Type} : (l : List α) → l.wrap.map (fun x => x.1) = l
| [] => by simp [wrap]
| a :: l => by {
  simp [map]
  exact List.wrap_canc l
}

theorem Tree.depth_subtree : (t : Tree) → (y: Tree) → y ∈ t.subtrees → y.depth < t.depth
| Tree.nil, y => by {
  intro hy
  simp [Tree.subtrees] at hy
}
| Tree.root _, y => by {
  simp [Tree.subtrees, Tree.depth]
}
| Tree.cons x t, y => by {
  simp [Tree.subtrees]
  intro h
  cases h with
  | inl l => {
    rw [l]
    simp [Tree.depth]
  }
  | inr r => {
    have := depth_subtree t y r
    simp [Tree.depth]
    exact Or.inr this
  }
}

def arity (t : Tree) : Nat := Id.run do
  let mut out : Nat := t.subtrees.length
  for ⟨y, hy⟩ in t.subtrees.wrap do
    out := max out (arity y + 1)
  return out
termination_by arity t => t.depth
decreasing_by {
  simp_wf
  exact t.depth_subtree y hy
}

#check List.set
def Tree.delete_root : Tree → Option Tree
| nil => none
| root _ => some nil
| cons a t => match a.delete_root, a.get_root with
  | some a', some x => some <| cons a' (t.set_root x)
  | _, _ => none
