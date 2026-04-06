import EMCM.Algebra.Structures
import EMCM.Util.Script

namespace EMCM.Algebra.ChainComplex
open Structures Structures.PrincipalRing

/-- A chain complex of the form ⋯ ← 0 ← R ← 0 ← ⋯ or ⋯ ← 0 ← R ← R ← 0 ← ⋯,
given by the generator(s) in Γ and, in the second case, the differential in R. -/
inductive AtomicComplex (Γ : Type u₁) (R : Type u₂) [Ring R] where
  /-- The complex given by the element 1 in degree 0. -/
  | One
  /-- A single generator x of degree d with ∂x = 0. -/
  | Single (x : Γ) (d : Nat)
  /-- A pair of generators x (degree d) and y (degree d+1) with ∂y = ηx. -/
  | Pair (x y : Γ) (d : Nat) (η : R)

variable [Ring R]

instance : One (AtomicComplex Γ R) where
  one := .One

namespace AtomicComplex

instance [ToString Γ] [ToString R] : ToString (AtomicComplex Γ R) where
  toString | .One => "(1)₀"
           | .Single x d => s!"({x}){d.subscript}"
           | .Pair x y d η => s!"({x}, {y}, {η}){d.subscript}"

/-- The degree of x. -/
def degree : AtomicComplex Γ R → Nat
  | .One => 0
  | .Single _ d | .Pair _ _ d _ => d

/-- Decompose a pair with zero differential into two single generators.
Throw away a pair where the differential is an isomorphism. -/
def tryDecompose [PrincipalRing R]
  : AtomicComplex Γ R → List (AtomicComplex Γ R)
  | g@.One | g@(.Single ..) => [g]
  | g@(.Pair x y d η) =>
    if η == 0
    then [Single x d, Single y (d + 1)]
    else if gcd η 0 == 1 then []
    else [g]

/-- Change the base ring to R' using a map R → R'. -/
def ringChange [PrincipalRing R'] (f : R → R')
  : AtomicComplex Γ R → List (AtomicComplex Γ R')
  | .One => [.One]
  | .Single x d => [.Single x d]
  | .Pair x y d η => tryDecompose (.Pair x y d (f η))
