-- refernce implementation based on do-unchained paper
import Lean

declare_syntax_cat stmt
syntax "do'" stmt : term
syntax "let" ident "←" stmt ";" stmt:1 : stmt
syntax term : stmt
macro:0 "let" x:ident ":=" e:term ";" s:stmt : stmt => `(stmt| let $x ← (pure $e); s)
syntax "let mut" ident ":=" term ";" stmt:1 : stmt
syntax "if" term "then" stmt "else" stmt:1 : stmt
macro "{" s:stmt "}" : stmt => `(stmt | $s)

syntax "d!" stmt : term
macro_rules | `(d! let $x ← $s; $s') => `((d! $s) >>= fun $x => (d! $s'))
declare_syntax_cat expander
syntax "expand!" expander "in" stmt : stmt
syntax "mut" ident : expander

macro_rules | `(stmt| expand! mut $y in $e:term) => `(stmt| StateT.lift $e)

syntax "return" : expander syntax "break" : expander syntax "lift" : expander

macro_rules
| `(stmt| expand! $exp in if $e then $s1:stmt else $s2:stmt) =>
`(stmt| if $e then expand! $exp in $s1 else expand! $exp in $s2)

macro_rules
| `(stmt| expand! mut $y in let $x ← $s; $s') =>
if x == y then
throw $ Lean.Macro.Exception.error x s!"cannot shadow 'mut' variable '{x.getId}'"
else
`(stmt| let $x ← expand! mut $y in $s; let $y ← get; expand! mut $y in $s')

macro_rules | `(d! let mut $x := $e:term; $s) => `(stmt | let $x := $e; StateT.run' (d! expand! mut $x in $s) $x)
macro:0 s1:stmt ";" s2:stmt : stmt => `(stmt | let x ← $s1; $s2)

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
