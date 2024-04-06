import Mathlib.Data.Real.Basic


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

-- get tree at position pointer
def Tree.get? : (pointer : List Nat) → (tree : Tree) → Option Tree
| List.nil, tree => some tree
| a :: l, tree =>
  match (tree.subtrees.get? a) with
  | some x => x.get? l
  | none => none

-- change the tree at position pointer
def Tree.set? : (pointer : List Nat) → (tree : Tree) → (leaf : Tree) → Option Tree
| List.nil, tree, leaf => some leaf
| a :: l, tree, leaf =>
  match (tree.subtrees.get? a) with
  | some x => x.set? l leaf
  | none => none

def List.get_parent_pointer : (pointer : List Nat) → Option (List Nat)
| List.nil => none
| a :: l => some l

-- def delete_self(self) -> bool:
--     """Removes the current node from the visualization and
--     returns whether the deletion was successful.

--     Only do this if this node has a parent tree.

--     Do not set self._parent_tree to None, because it might be used
--     by the visualiser to go back to the parent folder.
--     """
--     # (Task 4) Complete the body of this method
--     if self._parent_tree is None or self._expanded:
--         return False
--     self._parent_tree._subtrees.remove(self)

--     curr = self
--     while curr._parent_tree is not None:
--         curr = curr._parent_tree
--         curr.data_size -= self.data_size

--         if len(curr._subtrees) == 0:
--             curr._expanded = False
--     self.data_size = 0
--     return True

def delete_self (tree : Tree) (self : List Nat): Tree × Bool :=
  match tree.set? self Tree.nil with
  | some x => ⟨x, true⟩
  | none => ⟨tree, false⟩
