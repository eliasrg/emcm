import EMCM.Algebra.Structures
import EMCM.Util.Prime

namespace EMCM.Algebra
open Structures

set_option linter.unusedVariables false in
abbrev pLocal (p : Nat) := Int

instance (priority := high) (p : Nat) : PrincipalRing (pLocal p) where
  gcd m n := (m.gcd n).primeComponent p
  toInt := id
