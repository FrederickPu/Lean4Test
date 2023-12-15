#check String.length
#check List.range

#check Char.toNat
#eval "19283109".drop 1

#check String.Pos
def getDigit (s : String) (index : Nat) : Option Nat := Id.run do
  match s.get? ⟨index⟩ with
  | some u => if u.isDigit && u.toNat != 48 then return some (u.toNat - 48) else
      if (s.drop index).startsWith "one" then
        return some 1
      if (s.drop index).startsWith "two" then
        return some 2
      if (s.drop index).startsWith "three" then
        return some 3
      if (s.drop index).startsWith "four" then
        return some 4
      if (s.drop index).startsWith "five" then
        return some 5
      if (s.drop index).startsWith "six" then
        return some 6
      if (s.drop index).startsWith "seven" then
        return some 7
      if (s.drop index).startsWith "eight" then
        return some 8
      if (s.drop index).startsWith "nine" then
        return some 9
      return none
  | none => return none


def getSecret (s : String) : Int := Id.run do
  let mut flag1 := false
  let mut flag2 := false
  let mut fst := 0
  let mut snd := 0
  for i in List.range s.length do
    let curr := getDigit s i
    match curr with
    | some d =>
      if flag1 then
        snd := d
        flag2 := true
      else
        fst := d
        flag1 := true
    | none =>
      pure Unit.unit
  if flag2 then
    return 10 * fst + snd
  else
    return 10 * fst + fst

#eval getSecret "9fourcsjph86shfqjrxlfourninev"
def main : IO Unit := do
  let mut out := 0
  let input ← IO.FS.lines "small.txt"
  for line in input do
    out := out + getSecret line
    IO.println <| getSecret line
  IO.println out
