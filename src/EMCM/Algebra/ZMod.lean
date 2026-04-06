import EMCM.Algebra.Structures
import EMCM.Util.LaTeX

namespace EMCM.Algebra
open Structures

/-- The ring ℤ/Nℤ. -/
def ZMod : Nat → Type
  | 0 => Int
  | n + 1 => Fin (n + 1)

namespace ZMod

instance (N : Nat) : Repr (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance
instance (N : Nat) : ToString (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance
instance (N : Nat) : LaTeX (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance
instance (N : Nat) : Inhabited (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance
instance (N : Nat) : Hashable (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance
instance (N : Nat) : BEq (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance
instance (N : Nat) : DecidableEq (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance
instance (N x : Nat) : OfNat (ZMod N) x := by cases N <;> unfold ZMod <;> infer_instance
instance (N : Nat) : Neg (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance
instance (N : Nat) : Add (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance
instance (N : Nat) : Sub (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance
instance (N : Nat) : Mul (ZMod N) := by cases N <;> unfold ZMod <;> infer_instance

def toInt : {N : Nat} → ZMod N → Int
  | 0, x => x
  | _ + 1, x => x.toNat

def ofInt : {N : Nat} → Int → ZMod N
  | 0 => id
  | n + 1 => λ x => if x < 0
                    then -(Fin.ofNat (n + 1) x.natAbs)
                    else Fin.ofNat (n + 1) x.natAbs

instance (N : Nat) : Coe Int (ZMod N) where coe := ofInt
instance (N : Nat) : HMul Int (ZMod N) (ZMod N) where hMul := (· * ·)

instance : (N : Nat) → PrincipalRing (ZMod N)
  | 0 => inferInstanceAs (PrincipalRing Int)
  | N@(_ + 1) => { characteristic := N
                   toInt := toInt
                   gcd x y := (N.gcd (Int.gcd x.toInt y.toInt)) }
