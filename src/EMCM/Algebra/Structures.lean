-- TODO document

import EMCM.Algebra.Order

namespace EMCM.Algebra.Structures

class AbGrp A extends
  BEq A,
  Add A, Sub A, Neg A, Zero A,
  HMul Int A A

class Ring R extends AbGrp R, Mul R, One R, Coe Int R where
  characteristic : Order

instance [Ring R] : Coe Nat R where
  coe n := Int.ofNat n
instance [Ring R] (n : Nat) : OfNat R n where
  ofNat := Int.ofNat n

class PrincipalRing R extends Ring R where
  gcd : R → R → Nat -- TODO document why Nat and not R
  toInt : R → Int

instance : PrincipalRing Int where
  characteristic := 0
  coe := id
  gcd := Int.gcd
  toInt := id
