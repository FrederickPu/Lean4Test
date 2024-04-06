import Mathlib.Data.Real.Basic

inductive Tree (α : Type*)
| root : α → Tree α
| cons : Tree α → Tree α → Tree α

def Tree.subtrees {α : Type*} : Tree α → List (Tree α)
| Tree.root _ => []
| Tree.cons t T => t :: T.subtrees


-- def Tree.init {α : Type*} : α → List α → α
-- | n, [] => Tree.root n
-- | n, a :: l => Tree.cons a (Tree.init n l)

def Tree.depth {α : Type*} : Tree α → Nat
| Tree.root _ => 1
| Tree.cons t T => max (t.depth + 1) T.depth

def Tree.size {α : Type*} : Tree α → Nat
| Tree.root _ => 1
| Tree.cons t T => t.size + T.size

def Tree.set_root {α : Type*} : Tree α  → α → Tree α
| Tree.root n, _root => Tree.root _root
| Tree.cons t T, _root => Tree.cons t (T.set_root _root)

theorem Tree.set_root_cons {α : Type*} (t T: Tree α) (a : α) : Tree.set_root (Tree.cons t T) a = Tree.cons t (T.set_root a) := by
  simp [set_root]

theorem size_pos {α : Type*} : (t : Tree α) → t.size > 0
| Tree.root x => by simp [Tree.size]
| Tree.cons a t => by {
  simp [Tree.size]
  left
  exact size_pos a
}

theorem size_cons {α : Type*} (a t : Tree α) : t.size < (Tree.cons a t).size := by
{
  simp [Tree.size]
  exact size_pos a
}

def Tree.set_subtrees  {α : Type*} : Tree α  → List (Tree α) → Tree α
| Tree.root n, []=> Tree.root n
| Tree.root n, a::l => Tree.cons a ((Tree.root n).set_subtrees l)
| Tree.cons a t, x => t.set_subtrees x
termination_by set_subtrees x y => x.size + y.length
decreasing_by
  all_goals simp_wf
  all_goals simp [size_cons]

def Tree.get_root {α : Type*} : Tree α → α
| Tree.root n => n
| Tree.cons _ T => T.get_root

theorem Tree.get_root_cons {α : Type*} (t T : Tree α) : (Tree.cons t T).get_root = T.get_root := by
  simp [Tree.get_root]

def List.wrap {α : Type*} : (l : List α) → List (Subtype (fun x : α => x ∈ l))
| [] => []
| a :: l =>
  Id.run do
    let temp : List (Subtype (fun x => x ∈ a :: l)):= l.wrap.map (fun ⟨x, hx⟩ => ⟨x, mem_cons_of_mem a hx⟩)
    return ⟨a, mem_cons_self a l⟩ :: temp

theorem List.wrap_canc {α : Type*} : (l : List α) → List.map (fun x => x.1) (List.wrap l) = l
| [] => by simp [wrap]
| a :: l => by {
  simp [map]
  exact List.wrap_canc l
}

theorem List.wrap_map {α β : Type*} (f : α → β) : (l : List α) → (l.wrap.map (fun x => f x.1)) = l.map f
| [] => by simp [wrap]
| a :: l => by {
  simp [map]
  rw [← List.wrap_map f l]
  rfl
}

theorem Tree.depth_subtree {α : Type*}: (t : Tree α) → (y: Tree α) → y ∈ t.subtrees → y.depth < t.depth
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

def arity {α : Type*} (t : Tree α) : Nat := Id.run do
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
def Tree.delete_root {α : Type*} : Tree α → Option (Tree α)
| root _ => none
| cons a t => match t.delete_root with
  | some x => cons a x
  | none => none

-- get tree at position pointer
def Tree.get? {α : Type*} : (pointer : List Nat) → (tree : Tree α) → Option (Tree α)
| List.nil, tree => some tree
| a :: l, tree =>
  match (tree.subtrees.get? a) with
  | some x => x.get? l
  | none => none

#check Tree.get?

structure Pointer {α : Type*} (t : Tree α) where
  (address : List Nat)
  (valid : t.get? address ≠ none)

def Tree.get {α : Type*} (tree : Tree α) (pointer : Pointer tree)  : Tree α :=
  match h : tree.get? pointer.address with
  | some x => x
  | none => by
    apply False.elim
    simp [pointer.valid] at h

def Tree.subtrees_enumerate {α : Type*} (source : Tree α) (pointer : Pointer source) : List ((Pointer source) × Tree α) :=
  ((List.range (source.get pointer).subtrees.length).zip (source.get pointer).subtrees).map (fun ⟨x, y⟩ =>
    ⟨⟨pointer.address ++ [x], by {
      sorry
    }⟩, y⟩
  )


-- change the tree at position pointer
def Tree.set? {α : Type*} : (pointer : List Nat) → (tree : Tree α) → (leaf : Tree α) → Option (Tree α)
| List.nil, tree, leaf => some leaf
| a :: l, tree, leaf =>
  match (tree.subtrees.get? a) with
  | some x => x.set? l leaf
  | none => none


theorem bruh {α : Type*} (tree : Tree α) (pointer : Pointer tree) (leaf : Tree α) : tree.set? pointer.address leaf ≠ none :=
match h : tree.set? pointer.address leaf with
| some x => by simp
| none => by {
  apply False.elim
  match h1 : pointer.address with
    | List.nil => {
      rw [h1] at h
      simp [Tree.set?] at h
    }
    | List.cons a l => {
      simp [h1] at h
      simp only [Tree.set?] at h
      have := pointer.valid
      rw [h1] at this
      simp only [Tree.get?] at this
      match H : List.get? (Tree.subtrees tree) a  with
      | some x => {
        simp [H] at h
        simp [H] at this
        have := bruh x ⟨l, this⟩ leaf
        simp [Tree.set?] at this
        tauto
      }
      | none => {
        simp [H] at this
      }

    }
}
termination_by bruh tree pointer leaf => tree.depth
decreasing_by {
  simp_wf
  have : x ∈ tree.subtrees := by exact List.get?_mem H
  apply Tree.depth_subtree
  exact this
}

def Tree.set {α : Type*} (tree : Tree α) (pointer : Pointer tree) (leaf : Tree α): Tree α :=
  match h : tree.set? pointer.address leaf with
  | some x => x
  | none => by {
    have := bruh tree pointer leaf
    tauto
  }

def List.get_parent_pointer : (pointer : List Nat) → Option (List Nat)
| List.nil => none
| a :: l => some l

theorem Tree.set_cons_subtrees {α : Type*} (t : Tree α) : (T : Tree α) → (l : List (Tree α)) → (Tree.cons t T).set_subtrees l = (T.set_subtrees l)
| T, l => by simp [set_subtrees]

theorem Tree.set_subtrees_cons {α : Type*} (t : Tree α) : (l : List (Tree α)) → (T : Tree α) → T.set_subtrees (t :: l) = Tree.cons t (T.set_subtrees l)
| [], Tree.root x => by
  simp [set_subtrees, cons]
| a::l, Tree.root x => by
  simp [set_subtrees, cons]
| l, Tree.cons a T' => by
  simp [set_subtrees, cons]
  rw [set_subtrees_cons t l T']

theorem Tree.set_subtrees_set_root {α : Type*} (a : α) : (T : Tree α) → (l : List (Tree α))  → (T.set_root a).set_subtrees l = (T.set_subtrees l).set_root a
| root x, List.nil => by {
  simp [set_subtrees, set_root]
}
| root x, c::l => by {
  rw [set_subtrees_cons, set_subtrees_cons]
  rw [set_root_cons]
  rw [set_subtrees_set_root]
}
| cons t T, List.nil => by {
  simp [set_root, set_subtrees]
  exact set_subtrees_set_root a T List.nil
}
| cons t T, c::l => by {
  simp [set_subtrees, set_root]
  simp [set_subtrees_cons]
  rw [set_root_cons]
  apply congrArg
  exact set_subtrees_set_root a T l
}
termination_by set_subtrees_set_root a T l => T.size + l.length
decreasing_by
  sorry

-- TODO:: define a tree state monad
