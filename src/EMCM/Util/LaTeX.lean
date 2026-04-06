class LaTeX α where
  latex : α → String
export LaTeX (latex)

def latexMath [LaTeX α] (x : α) : String :=
  s!"${latex x}$"

instance : LaTeX Int where
  latex := toString

instance (n : Nat) : LaTeX (Fin n) where
  latex := toString

instance : LaTeX String where
  latex := id
