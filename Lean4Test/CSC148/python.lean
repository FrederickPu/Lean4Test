import Mathlib.Tactic

mutual
  inductive PyExpr : Type where
    | None : PyExpr
    | of_BinOp : BinOp → PyExpr
    | of_PNum : Num → PyExpr
    | of_PBool : PBool → PyExpr
  inductive PBool : Type where
    | of_nat : Bool → PBool
  inductive PNum : Type where
    | of_int : Int → PNum
    | of_float : Float → PNum
  inductive BinOp : Type where
    | add : PyExpr → PyExpr → BinOp
end

def PyExpr.size : PyExpr → Nat
| None => 1
| of_BinOp (BinOp.add x y)=> x.size + y.size + 1
| of_PNum _ => 1
| of_PBool _ => 1

def BinOp.size : BinOp → Nat
| BinOp.add x y => x.size + y.size + 1

inductive PyValue : Type where
  | None : PyValue
  | of_bool : Bool → PyValue
  | of_int : Int → PyValue
  | of_float : Float → PyValue

theorem PyExpr.size_pos : (x : PyExpr) → 0 < x.size
| None => by simp [PyExpr.size]
| of_BinOp  (BinOp.add x y) => by simp [PyExpr.size]
| of_PNum x => by simp [PyExpr.size]
| of_PBool x => by simp [PyExpr.size]


mutual
def BinOp.evaluate : BinOp → PyValue
  | BinOp.add x y => aux x y
  where aux (x y : PyExpr) : PyValue :=
    match x.evaluate, y.evaluate with
    | PyValue.of_int x, PyValue.of_int y => PyValue.of_int (x + y)
    | _, _ => PyValue.None
def PyExpr.evaluate : PyExpr → PyValue
  | PyExpr.None => PyValue.None
  | PyExpr.of_BinOp x => x.evaluate
  | _ => PyValue.None
end
termination_by
  evaluate.aux x y => x.size + y.size
  PyExpr.evaluate x => x.size
  BinOp.evaluate x => x.size
decreasing_by
  all_goals simp_wf; simp [PyExpr.size_pos, BinOp.size, PyExpr.size]f
