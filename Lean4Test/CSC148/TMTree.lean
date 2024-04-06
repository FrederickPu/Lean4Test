import Lean4Test.CSC148.Tree


-- === Public Attributes ===
--     rect:
--         The pygame rectangle representing this node in the treemap
--         visualization.
--     data_size:
--         The size of the data represented by this tree.

--     === Private Attributes ===
--     _colour:
--         The RGB colour value of the root of this tree.
--     _name:
--         The root value of this tree, or None if this tree is empty.
--     _subtrees:
--         The subtrees of this tree.
--     _parent_tree:
--         The parent tree of this tree; i.e., the tree that contains this tree
--         as a subtree, or None if this tree is not part of a larger tree.
--     _expanded:
--         Whether or not this tree is considered expanded for visualization.
structure TMTreeProps where
  (rect : Nat × Nat × Nat × Nat)
  (data_size : Nat)
  (_colour : Float × Float × Float)
  (_name : Option String)
  (_parent_tree : List Nat) -- pointer
  (_expanded : Bool)

def TMTreeProps.set_data_size : TMTreeProps → Nat → TMTreeProps :=
  fun ⟨a, data_size, b, c, d, e⟩ n => ⟨a, n, b, c, d, e⟩

def TMTree := Tree TMTreeProps

def TMTree.set_data_size : TMTree → Nat → TMTree :=
  fun t n => t.set_root (t.get_root.set_data_size n)

def TMTree.is_empty : TMTree → Bool
| Tree.root x => x._name = none
| Tree.cons t T => TMTree.is_empty T


#check Tree.get

#check Tree
def update_data_size : TMTree → TMTree
| Tree.root x => Tree.root x
| Tree.cons t T => Tree.cons (update_data_size t) ((update_data_size  T).set_data_size ((update_data_size t).get_root.data_size + (update_data_size T).get_root.data_size))

def update_data_size_iter : TMTree → TMTree
| Tree.root x => Tree.root x
| t =>
  (t.set_subtrees (t.subtrees.wrap.map (fun x => update_data_size_iter x.val))).set_root <| t.get_root.set_data_size (t.subtrees.wrap.map (fun x => (update_data_size_iter x.val).get_root.data_size)).sum
termination_by update_data_size_iter t => t.depth
decreasing_by
  all_goals simp_wf;
  all_goals simp [x.property, Tree.depth_subtree]

def List.sum_cons {α : Type*} (a : α) [Zero α] [Add α] (l : List α) : (a :: l).sum = a + l.sum := by
  sorry

theorem crux : (T : TMTree) → (update_data_size_iter T).get_root.data_size = T.subtrees
theorem wow : ∀ (t T : TMTree), update_data_size_iter (Tree.cons t T) = Tree.cons (update_data_size_iter t) (TMTree.set_data_size (update_data_size_iter T) ((update_data_size_iter t).get_root.data_size + (update_data_size_iter T).get_root.data_size))
| t, T => by {
  simp [update_data_size_iter]
  let f := fun x => ((Tree.get_root (update_data_size_iter x)).data_size)
  have : List.sum (List.map (fun x => (Tree.get_root (update_data_size_iter x.val)).data_size)
          (List.wrap (Tree.subtrees (Tree.cons t T)))) = List.sum (List.map (fun x => f x.val) (List.wrap (Tree.subtrees (Tree.cons t T)))) := by
          simp
  rw [this]
  rw [List.wrap_map, List.wrap_map]
  simp [Tree.subtrees, List.map_cons]
  simp [List.sum_cons]
}
theorem wee : ∀ x, update_data_size x = update_data_size_iter x
| Tree.root x => by {
  simp [update_data_size, update_data_size_iter]
}
| Tree.cons t T => by {
  simp only [update_data_size, update_data_size_iter]
  let f := fun x => ((Tree.get_root (update_data_size_iter x)).data_size)
  have : List.sum (List.map (fun x => (Tree.get_root (update_data_size_iter x.val)).data_size)
          (List.wrap (Tree.subtrees (Tree.cons t T)))) = List.sum (List.map (fun x => f x.val) (List.wrap (Tree.subtrees (Tree.cons t T)))) := by
          simp
  rw [this]
  rw [List.wrap_map, List.wrap_map]

  simp [ Tree.subtrees, Tree.cons]
  rw [wee T, wee t]
  simp [Tree.set_subtrees_cons, Tree.set_root]
  apply congrArg
  rw [List.sum_cons]
  rw [Tree.get_root_cons, Tree.set_cons_subtrees]
  -- rw [← Tree.set_subtrees_set_root]
  simp [TMTree.set_data_size]
}

#check Tree.set_subtrees_set_root
