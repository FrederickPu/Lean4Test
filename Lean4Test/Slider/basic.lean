import Mathlib.Data.Matrix.Basic

-- 1 2
-- 3 _
#check Matrix (Fin 2) (Fin 2) (Option (Fin 3))

def up : Matrix (Fin 2) (Fin 2) (Option (Fin 3)) → Matrix (Fin 2) (Fin 2) (Option (Fin 3))
