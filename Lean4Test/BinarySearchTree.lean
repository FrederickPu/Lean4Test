import Mathlib.Tactic

inductive BinaryTree
| nil : BinaryTree
| mk (root : Nat) (left : BinaryTree) (right : BinaryTree) : BinaryTree


def BinaryTree.depth : BinaryTree → Nat
| BinaryTree.nil => 0
| BinaryTree.mk root left right => 1 + left.depth + right.depth

def BinaryTree.delete_smallest : BinaryTree → (BinaryTree × Nat)
| BinaryTree.mk root left right =>
  match left, right with
  | nil, nil => ⟨nil, root⟩
  | nil, mk rroot rleft rright => ⟨mk rroot rleft rright, root⟩
  | mk lroot lleft lright, _ => ⟨BinaryTree.mk root (mk lroot lleft lright).delete_smallest.1 right, (mk lroot lleft lright).delete_smallest.2⟩
| BinaryTree.nil => ⟨nil, 0⟩

def BinaryTree.delete_root : BinaryTree → BinaryTree
| BinaryTree.mk root left right =>
  match left, right with
  | nil, nil => BinaryTree.nil
  | nil, BinaryTree.mk rroot rleft rright => (BinaryTree.mk rroot rleft rright)
  | BinaryTree.mk lroot lleft lright, nil => BinaryTree.mk lroot lleft lright
  | BinaryTree.mk lroot lleft lright, BinaryTree.mk rroot rleft rright => BinaryTree.mk (BinaryTree.mk rroot rleft rright).delete_smallest.2 (BinaryTree.mk lroot lleft lright) (BinaryTree.mk rroot rleft rright).delete_smallest.1
| BinaryTree.nil => nil

def BinaryTree.contains : BinaryTree → Nat → Prop
| BinaryTree.mk root left right, n => root = n ∨ left.contains n ∨ right.contains n
| BinaryTree.nil, _ => False

instance : Membership Nat BinaryTree :=
{
  mem := fun B x => BinaryTree.contains x B
}


def BinaryTree.isSearch : BinaryTree → Prop
| BinaryTree.mk root left right => (∀ x ∈ left, x < root) ∧ (∀ y ∈ right, root < y) ∧ left.isSearch ∧ right.isSearch
| BinaryTree.nil => True

def BinaryTree.delete_smallest_mem : (t : BinaryTree) → (∃ x : ℕ, x ∈ t) → t.delete_smallest.2 ∈ t
| nil => by simp [delete_smallest, Membership.mem, contains]
| mk root left right => by {
  intro h
  match left, right with
  | nil, nil => simp [delete_smallest, Membership.mem, contains]
  | nil, mk rroot rleft rright => {
    simp [delete_smallest, Membership.mem, contains]
  }
  | mk lroot lleft lright, right =>{
    apply Or.inr ∘ Or.inl
    apply delete_smallest_mem
    use lroot
    simp [Membership.mem, contains]
  }
}
def BinaryTree.delete_smallest_sub : {t : BinaryTree} → {x | x ∈ t.delete_smallest.1} ⊆ {x | x ∈ t}
| nil => by simp [delete_smallest]
| mk root left right => by {
  match left, right with
  | nil, nil => tauto
  | nil, mk rroot rleft rright => tauto
  | mk lroot lleft lright, _ =>
  intro a ha

  cases ha with
  | inl l => tauto
  | inr r => cases r with
  | inl rl =>
    have := delete_smallest_sub rl
    tauto
  | inr rr => tauto
}
def BinaryTree.root_mem (root : Nat) (left right : BinaryTree) : root ∈ mk root left right := by
  simp [Membership.mem, contains]


def BinaryTree.delete_smallest_lt : (t : BinaryTree) → t.isSearch → ∀ x ∈ t.delete_smallest.1, t.delete_smallest.2 < x
| nil => by
  intro h x hx
  apply False.elim
  exact hx
| BinaryTree.mk root left right => by
  intro H x hx
  match left, right with
  | nil, nil => simp [delete_smallest, Membership.mem, contains] at hx
  | nil, mk rroot rleft rright =>
    simp [delete_smallest]
    rw [delete_smallest] at hx
    rw [isSearch] at H
    linarith [H.2.1 x hx]
  | mk lroot lleft lright, right => {
    simp [delete_smallest]
    rw [isSearch] at H
    cases hx with
    | inl l => {
      rw [← l]
      have := delete_smallest_mem (mk lroot lleft lright) (by {
        use lroot
        exact BinaryTree.root_mem lroot lleft lright
      })
      have := H.1 _ this
      linarith
    }
    | inr r => cases r with
    | inl rl =>
      apply BinaryTree.delete_smallest_lt
      exact H.2.2.1
      exact rl
    | inr rr =>
      have := delete_smallest_mem (mk lroot lleft lright) (by {
        use lroot
        exact BinaryTree.root_mem lroot lleft lright
      })
      linarith [H.1 _ this,  H.2.1 x rr]
  }

theorem BinaryTree.delete_smallest_isSearch : {t : BinaryTree} → t.isSearch →  t.delete_smallest.1.isSearch
| nil => by {
  intro h
  simp [delete_smallest]
  exact h
}
| mk root left right => by {
  intro h
  match left, right with
  | nil, nil => {
    simp [delete_smallest, isSearch]
  }
  | nil, mk rroot rleft rright => {
    simp [delete_smallest]
    exact h.2.2.right
  }
  | mk lroot lleft lright, right =>{
    simp [delete_smallest, isSearch]
    apply And.intro
    intro x hx
    have := delete_smallest_sub hx
    exact h.1 _ this

    use h.2.1
    apply And.intro
    apply delete_smallest_isSearch
    exact h.2.2.left
    exact h.2.2.right
  }
}

theorem BinaryTree.mem_nil : ∀ x, x ∈ nil → False := by {
  intro x hx
  exact hx
}
theorem BinaryTree.delete_root_isSearch : (B : BinaryTree) → B.isSearch → B.delete_root.isSearch
| nil => by {
  intro h
  simp [isSearch]
}
| mk root left right => by {
  intro h
  match left, right with
  | nil, nil => simp [isSearch, delete_root]
  | nil, mk rroot rleft rright => exact h.2.2.2
  | mk lroot lleft lright, nil => exact h.2.2.1
  | mk lroot lleft lright, mk rroot rleft rright => {
    simp [delete_root]
    apply And.intro
    intro x hx
    apply Nat.lt_trans
    exact h.1 x hx
    exact h.2.1 _ (delete_smallest_mem (mk rroot rleft rright) (by {
      use rroot
      apply root_mem
    }))

    apply And.intro
    intro y hy
    have := delete_smallest_lt (mk rroot rleft rright) h.2.2.right
    exact this y hy

    use h.2.2.left
    exact delete_smallest_isSearch h.2.2.right
  }
}
