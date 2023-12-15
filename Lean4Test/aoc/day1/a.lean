-- import Mathlib.Data.List.Sort

-- #check List.mergeSort
-- def part1 (xs : List Int) : Int := xs.foldl max 0

-- def part2 (xs : List Int) : Int := (xs.mergeSort (fun x y => x < y)) |>.reverse |>.take 3 |>.foldl .add 0

-- #check Char.isDigit
-- #eval Char.toNat '0'
-- #eval Char.toNat '9'
def getSecret (s : String) : Int := Id.run do
 let mut flag := false
 let mut flag1 := false
 let mut fst := 0
 let mut snd := 0
 for c in s.toList do
  if c.isDigit then
    if flag then
      snd := c.toNat - 48
      flag1 := true
    else
      fst := c.toNat - 48
      flag := true
 if flag1 then
  return 10 * fst + snd
 else
  return 10 * fst + fst


#eval "aalskdjk what alskjdl".splitOn "what"
#check String.contains
#check String.endsWith
#check String.startsWith

-- #check IO.getStdin
def main : IO Unit := do
  let mut out := 0
  let input ← IO.FS.lines "small.txt"
  for line in input do
    out := out + getSecret line
    IO.println <| getSecret line
  IO.println out
