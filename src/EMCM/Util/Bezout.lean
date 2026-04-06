/-- Integers (x, y) such that x * m + y * n = gcd m n. -/
def Nat.bezout (m n : Nat) : Int × Int :=
  if m = 0 then (0, 1)
  else let (x, y) := bezout (n % m) m
       (y - x * (n / m), x)
termination_by m
decreasing_by exact mod_lt n (zero_lt_of_ne_zero ‹m ≠ 0›)

/-- Integers (x, y) such that x * m + y * n = gcd m n. -/
def Int.bezout (m n : Int) : Int × Int :=
  let (x, y) := m.natAbs.bezout n.natAbs
  (m.sign * x, n.sign * y)
