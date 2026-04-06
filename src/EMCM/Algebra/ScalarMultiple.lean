import EMCM.Algebra.Structures

namespace EMCM.Algebra
open Structures

/-- A scalar multiple of an element of Γ, with coefficients in A. -/
inductive ScalarMultiple (Γ : Type _) A [AbGrp A] where
  /-- The zero scalar multiple. -/
  | Zero
  /-- A nonzero scalar multiple of an element of Γ.
Use the SMul and Coe instances instead of this constructor
to ensure coeff is nonzero. -/
  | Mul (coeff : A) (gen : Γ)
  deriving Inhabited, BEq

instance [AbGrp A] : Zero (ScalarMultiple Γ A) where
  zero := .Zero

namespace ScalarMultiple
variable [AbGrp A]

/-- Change `.Mul 0 g` into `.Zero`. -/
def normalize : ScalarMultiple Γ A → ScalarMultiple Γ A
  | .Zero => .Zero
  | m@(.Mul c _) => if c == 0 then .Zero else m

instance [Ring R] : SMul R (ScalarMultiple Γ R) where
  smul r | .Zero => .Zero
         | .Mul c g => normalize (.Mul (r * c) g)

instance [Ring R] : SMul Int (ScalarMultiple Γ R) where
  smul r x := (r : R) • x

instance [Ring R] : SMul Nat (ScalarMultiple Γ R) where
  smul r x := (r : R) • x

instance [Ring R] : Coe Γ (ScalarMultiple Γ R) where
  coe g := normalize (.Mul 1 g)

/- instance (priority := mid) [ToString A] [ToString Γ] -/
/-   : ToString (ScalarMultiple Γ A) where -/
/-   toString | .Zero => "0" -/
/-            | .Mul c g => s!"{c}{g}" -/

instance [Ring A] [ToString A] [ToString Γ] : ToString (ScalarMultiple Γ A) where
  toString | .Zero => "0"
           | .Mul c g => if c == 1 then s!"{g}"
                         else if c == -1 then s!"-{g}"
                         else s!"{c}{g}"

instance [Ring A] [LaTeX A] [LaTeX Γ] : LaTeX (ScalarMultiple Γ A) where
  latex | .Zero => "0"
        | .Mul c g => if c == 1 then s!"{latex g}"
                      else if c == -1 then s!"-{latex g}"
                      else s!"{latex c} {latex g}"

def mapCoeff [AbGrp A'] (f : A → A')
  : ScalarMultiple Γ A → ScalarMultiple Γ A'
  | .Zero => .Zero
  | .Mul c g => .Mul (f c) g
