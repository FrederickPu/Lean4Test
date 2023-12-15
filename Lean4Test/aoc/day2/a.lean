def isVatringlid (s : String) : Bool := Id.run do
  let m := s.splitOn ";"

#check String.join
#eval String.join ("l llkj ".splitOn " ")
#eval String.toNat! "12381902"
def main : IO Unit := do
  let mut out := 0
  let input ← IO.FS.lines "small.txt"
  for line in input do
    out := out + getSecret line
    IO.println <| getSecret line
  IO.println out
