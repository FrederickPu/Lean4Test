-- refernce implementation based on do-unchained paper
import Lean

declare_syntax_cat stmt
syntax "do'" stmt : term

-- s ∈ Stmt ::= e
--              | let ← s; s'
syntax term : stmt
syntax "let" ident "←" stmt ";" stmt:1 : stmt

syntax "let mut" ident ":=" term ";" stmt:1 : stmt
syntax ident ":=" term : stmt
syntax "if" term "then" stmt "else" stmt:1 : stmt

syntax "d!" stmt : term
-- (D1)
macro_rules | `(d! $t:term) => `($t)
-- (D2)
macro_rules | `(d! let $x ← $s; $s') => `((d! $s) >>= fun $x => (d! $s'))

declare_syntax_cat expander
syntax "expand!" expander "in" stmt : stmt
syntax "mut" ident : expander

-- (D3)
macro_rules | `(d! let mut $x := $e:term; $s) => `(stmt | let $x := $e; StateT.run' (d! expand! mut $x in $s) $x)
-- (S1)
macro_rules | `(stmt| expand! mut $y in $e:term) => `(stmt| StateT.lift $e)
-- (S2)
macro_rules
| `(stmt| expand! mut $y in let $x ← $s; $s') =>
  if x == y then
      throw $ Lean.Macro.Exception.error x s!"cannot shadow 'mut' variable '{x.getId}'"
  else
    `(stmt | let $x ← expand! mut $y in $s; let $y ← get; expand! mut $y in $s')


syntax "return" : expander syntax "break" : expander syntax "lift" : expander

-- general case for let $x ← $e; $s
-- (R3) (B4) (L4)
macro_rules
| `(stmt| expand! mut $y in let $x ← $s; $s') =>
`(stmt | let $x ← expand! mut $y in $s; let $y ← get; expand! mut $y in $s')

-- (S6), (R6), (B7), (L7)
macro_rules
| `(stmt| expand! $exp in if $e then $s1:stmt else $s2:stmt) =>
`(stmt| if $e then expand! $exp in $s1 else expand! $exp in $s2)

-- Note: S_y = mut y
-- (S4), (S5)
macro_rules
| `(stmt| expand! mut $y in $x:ident := $e) =>
  if x == y then
    `(stmt | set $x)
  else
    `(stmt | x := $e)

-- (S3)
macro_rules
| `(stmt| expand! mut $y in let $x ← $s; $s') =>
if x == y then
  throw $ Lean.Macro.Exception.error x s!"cannot shadow 'mut' variable '{x.getId}'"
else
  `(stmt| let $x ← expand! mut $y in $s; let $y ← get; expand! mut $y in $s')
-- general case for let mut $x := $e
-- (R4) (B5) (L5)
macro_rules
| `(stmt| expand! $exp in let mut $x:ident := $e; $s) =>
`(stmt| let mut $x:ident := $e; expand! $exp in $s)
-- general case for $x := $e
-- (R5) (B6) (L6)
macro_rules
| `(stmt| expand! $exp in $x:ident := $e) => `(stmt | $x:ident := $e)

syntax "return" term : stmt
-- (R1)
macro_rules
| `(stmt| expand! return in return $e) => `(stmt| throw $e)
-- (R2)
macro_rules
| `(stmt| expand! return in $e:term) => `(stmt| ExceptT.lift $e)


-- (A1)
macro:0 "let" x:ident ":=" e:term ";" s:stmt : stmt => `(stmt| let $x ← (pure $e); s)
-- (A2)
macro:0 s1:stmt ";" s2:stmt : stmt => `(stmt | let x ← $s1; $s2)
macro "{" s:stmt "}" : stmt => `(stmt | $s)

theorem simple [Monad m] [LawfulMonad m] (b : Bool) (ma ma' : m α) :
  (do' let x ← ma;if b then { x ← ma' };pure x) = (ma >>= fun x => if b then ma' else pure x) :=
  by cases b <;> simp

theorem eq_findSomeM_findM [Monad m] [LawfulMonad m] (xss : List (List α)) :
        (do' for xs in xss do'{
          for x in xs do' {
            let b ← p x;
            if b then {
              return some x
            }
          }
          };
          pure none)
        = List.findSomeM? (fun xs => List.findM? p xs) xss := by
  induction xss with
  | nil => simp [List.findSomeM?]
  | cons xs xss' ih =>
    simp [List.findSomeM?]
    rw [← ih, ← eq_findM]
    induction xs with
    | nil => simp
    | cons x xs' ih =>
      simp;
      apply byCases_Bool_bind <;> simp [ih]
