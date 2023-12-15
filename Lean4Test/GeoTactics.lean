import Mathlib.Lean.Expr.Basic

#check List.filterTR
#check List.filterMap

#eval [some 1, some 2, some 3, none, some 5].filterMap (fun x => x)

/-- Uniform at random in [0, 1)-/
def randomFloat {gen} [RandomGen gen] (g : gen) : Float × gen :=
  let (n, g') := RandomGen.next g
  let (lo, hi) := RandomGen.range g
  (Float.ofNat (n - lo) / Float.ofNat (hi - lo + 1), g')

def IO.randFloat (lo := 0.0) (hi := 1.0) : IO Float := do
  let gen ← IO.stdGenRef.get
  let (r, gen) := randomFloat gen
  IO.stdGenRef.set gen
  return lo + (hi - lo) * r

def IO.randPoint (lo := 0.0) (hi := 1.0) : IO (Float × Float) := do
  return ⟨← IO.randFloat lo hi, ← IO.randFloat lo hi⟩


open Lean

#check Eq
#check HAdd.hAdd
partial def isEq (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``Eq, #[_, e1, e2]) => true
  | _ => false

universe u
class Bet (α : Type u) where
  (bet : α → α → α → Prop)

partial def isBet (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Bet.bet, #[_, _, e1, e2, e3]) => (e1, e2, e3) -- eg ::  [Int, inst, 1, 2, 3]
  | _ => none

#check List.mmap

structure BetSeq
  (exprMap : ExprMap Nat)
  (betOps : List (Nat × Nat × Nat))

#check Float
#check Elab.Tactic.TacticM
#check HashMap.contains
#check HashMap.find!
#eval (1.0, 2.0) + (3.0, 4.0)

instance : HAdd (Float × Float) (Float × Float) (Float × Float) := {
  hAdd := fun ⟨a, b⟩ => fun ⟨d, e⟩ => (a + d, b + e)
}
instance : HSub (Float × Float) (Float × Float) (Float × Float) := {
  hSub := fun ⟨a, b⟩ => fun ⟨d, e⟩ => (a - d, b - e)
}
instance : HMul (Float × Float) Float (Float × Float) := {
  hMul := fun ⟨a, b⟩ => fun c => (a * c, b * c)
}

#check TacticM
def randomRay : Float × Float := (1, 0)
def updateCandidate (exprMap : ExprMap (Float × Float)) (betOp : Expr × Expr × Expr) : ((ExprMap (Float × Float))) × (List (Nat × Nat)) := Id.run
 do
  let ⟨a, b, c⟩ := betOp
  return ⟨
  match exprMap.contains a, exprMap.contains b, exprMap.contains c with
  | false, true, true => exprMap.insert a ((exprMap.find! b) - (exprMap.find! c) + exprMap.find! b)
  | true, false, true => exprMap.insert b ((exprMap.find! a + exprMap.find! c)*0.5)
  | true, true, false =>  exprMap.insert c ((exprMap.find! b) - (exprMap.find! a) + exprMap.find! b)
  | true, false, false => (exprMap.insert b (exprMap.find! a + randomRay)).insert c (exprMap.find! a + randomRay + randomRay)
  | false, true, false => (exprMap.insert a (exprMap.find! b - randomRay)).insert c (exprMap.find! b + randomRay)
  | false, false, true => (exprMap.insert b (exprMap.find! c + randomRay)).insert a (exprMap.find! c + randomRay + randomRay)
  | false, false, false => _
  | true, true, true => exprMap
  ,
  _⟩


open Elab Tactic

syntax (name := wowTacStx) "wow " : tactic

@[tactic wowTacStx]
def wow : Tactic
  | stx@`(tactic| wow) => withMainContext do
    let mut out : List (Nat × Nat × Nat) := []
    let mut exprMap : ExprMap Nat := ∅
    let mut points : HashMap Nat (Float × Float) := ∅
    let mut vertices : List (Nat × Nat) := []
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    for decl in ctx do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- **NEW:** Find the type.
      match isBet declType with
      | some (a, b, c) =>
        if !exprMap.contains a then
          exprMap := exprMap.insert a exprMap.size
        if !exprMap.contains b then
          exprMap := exprMap.insert b exprMap.size
        if !exprMap.contains c then
          exprMap := exprMap.insert c exprMap.size
        let a' := exprMap.find! a
        let b' := exprMap.find! b
        let c' := exprMap.find! c
        if ! (vertices.contains (a', b') ∨ vertices.contains (b', a')) then
            vertices := vertices.cons (a', b')
        if ! (vertices.contains (b', c') ∨ vertices.contains (c', b')) then
          vertices := vertices.cons (b', c')

        let p1 ← IO.randPoint
        let p2 ← IO.randPoint
        match points.contains a', points.contains b', points.contains c' with
        | false, true, true =>
          points := points.insert a' ((points.find! b') - (points.find! c') + points.find! b')
        | true, false, true =>
          points := points.insert b' ((points.find! a' + points.find! c')*0.5)
        | true, true, false =>
          points := points.insert c' ((points.find! b') - (points.find! a') + points.find! b')
        | true, false, false =>
          points := points.insert b' (points.find! a' + p1)
          points := points.insert c' (points.find! a' + p1 + p1)
        | false, true, false =>
          points := points.insert a' (points.find! b' - p1)
          points := points.insert c' (points.find! b' + p1)
        | false, false, true =>
          points := points.insert b' (points.find! c' + p1)
          points := points.insert a' (points.find! c' + p1 + p1)
        | false, false, false =>
          points := (points.insert a' p1).insert b' (p1 + p2)
          points := points.insert c' (p1 + p2 + p2)
        | true, true, true => points := points
        out := List.cons (exprMap.find! a, exprMap.find! b, exprMap.find! c) out
      | none => pure ()
    dbg_trace f!"{out}"
      -- let declExpr := decl.toExpr -- Find the expression of the declaration.
      -- let declName := decl.userName -- Find the name of the declaration.
      -- let declType ← Lean.Meta.inferType declExpr -- **NEW:** Find the type.
      -- match isBet declType with
      -- | some x => dbg_trace f!"+ local decl: name: {declName} | isEq : {isEq declType} | isBet : {x}"
      -- | none => pure ()
  | _ => throwUnsupportedSyntax

#check Expr.eqv
#check ExprSet

example {α : Type} [Bet Int] : Bet.bet (1 : Int) 2 3 → Bet.bet (1 : Int) (1 + 1) 3 → 1 + 1 = 2 := by
  intro h h1
  wow

#check Lean.Meta.getLocalHyps
#check ExprMap
#check HashMap.find!
#check Expr.instHashableExpr
#check Expr
