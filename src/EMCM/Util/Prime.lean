import Std.Data.Iterators

/-- The `p`-adic valuation of `n`
(the largest `i` such that `p^i` divides `n`). -/
def Nat.νp (n p : Nat) : Nat :=
  if p ≤ 1 ∨ n = 0 ∨ n % p ≠ 0 then 0
  else 1 + νp (n / p) p
decreasing_by
  apply div_lt_self <;> grind only

/-- The largest `p^i` dividing `n`. -/
def Nat.primeComponent (n p : Nat) : Nat :=
  if p = 0 then n else p^(n.νp p)

/-- Is `n` a power of `p`? -/
def Nat.isPowerOf (n b : Nat) : Bool :=
  if b = 0 then n == 0
  else if b = 1 then n == 1
  else if n ≤ 1 then n == 1
  else let d := n / b
       n == d * b ∧ d.isPowerOf b
  decreasing_by
    apply Nat.div_lt_of_lt_mul
    apply (Nat.lt_mul_iff_one_lt_left ?_).mpr
    <;> grind only

/-- The prime numbers up to and including `N`. -/
def Nat.primesUpTo (N : Nat) := sieve (2...=N).toList
where
  sieve | [] => []
        | p :: ns => p :: sieve (ns.filter (· % p != 0))
  termination_by ls => ls.length
  decreasing_by
    simp
    apply lt_succ_of_le
    apply List.length_filter_le

/-- Prime factorisation as a list of (prime, power). -/
def Nat.factor (n : Nat) : List (Nat × Nat) :=
  factorsFrom (Nat.primesUpTo n) n
where
  factorsFrom
  | [], _ => []
  | p :: ps, n =>
    let f := n.νp p
    if f == 0 then factorsFrom ps n
    else (p, f) :: factorsFrom ps (n / p^f)

/-- Is `n` a prime? -/
def Nat.isPrime (n : Nat) : Bool :=
  n ≥ 2 ∧ n.factor == [(n, 1)]
