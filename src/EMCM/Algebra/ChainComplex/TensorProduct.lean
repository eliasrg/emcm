-- TODO document

import EMCM.Algebra.Structures
import EMCM.Algebra.ChainComplex.AtomicComplex

namespace EMCM.Algebra.ChainComplex.TensorProduct
open Structures ChainComplex PrincipalRing

/-- A generator in a nontrivial atomic complex of a
tensor product C₁ ⊗ C₂ ⊗ ⋯ (where "nontrivial" means
"not of the form 0 ← R ← R ← 0 with an isomorphism
in the middle"). -/
inductive TPGenerator (Γ : Type u) where
  /-- A generator of an individual complex. -/
  | Basic (g : Γ)
  /-- A tensor product of a basic generator with something else. -/
  | Prod (g : Γ) (t : TPGenerator Γ)
  /-- If n₁x₁ = ∂y₁ and n₂x₂ = ∂y₂, the element
n₁/gcd(n₁,n₂) x₁y₂ - (-1)^|y₁| n₂/gcd(n₁,n₂) y₁x₂. -/
  | τ (x₁ y₁ : Γ) (x₂ y₂ : TPGenerator Γ)
  /-- If η₁x₁ = ∂y₁ and η₂x₂ = ∂y₂, the element
a y₁x₂ + (-1)^|x₁| b x₁y₂
where a and b are Bézout coefficients with
aη₁ + bη₂ = gcd(η₁,η₂). -/
  | κ (x₁ y₁ : Γ) (x₂ y₂ : TPGenerator Γ)
  deriving Inhabited, BEq

variable {Γ : Type u₁} {R : Type u₂} [PrincipalRing R]

instance [ToString Γ] : ToString (TPGenerator Γ) where
  toString := helper
  where helper
  | .Basic h => toString h
  | .Prod a₁ a₂ => s!"{a₁}⊗{helper a₂}"
  | .τ x₁ y₁ x₂ y₂ => s!"τ({x₁},{y₁},{helper x₂},{helper y₂})"
  | .κ x₁ y₁ x₂ y₂ => s!"κ({x₁},{y₁},{helper x₂},{helper y₂})"

instance [LaTeX Γ] : LaTeX (TPGenerator Γ) where
  latex := helper
  where helper
  | .Basic h => latex h
  | .Prod a₁ a₂ => s!"{latex a₁} \\otimes {helper a₂}"
  | .τ x₁ y₁ x₂ y₂ => s!"\\tau({latex x₁},{latex y₁},{helper x₂},{helper y₂})"
  | .κ x₁ y₁ x₂ y₂ => s!"\\kappa({latex x₁},{latex y₁},{helper x₂},{helper y₂})"

def basicAtomicComplex
  : AtomicComplex Γ R → AtomicComplex (TPGenerator Γ) R
  | .One => .One
  | .Single x d => .Single (.Basic x) d
  | .Pair x y d η => .Pair (.Basic x) (.Basic y) d η

def tensor₂AtomicComplexes
  (maxDeg : Nat)
  (C₁ : List (AtomicComplex Γ R))
  (C₂ : List (AtomicComplex (TPGenerator Γ) R))
  : List (AtomicComplex (TPGenerator Γ) R) :=
  List.filter (·.degree ≤ maxDeg) <|
    C₁.flatMap λ c₁ =>
    C₂.flatMap λ c₂ =>
    match c₁, c₂ with
    | .One, _ => [c₂]
    | _, .One => [basicAtomicComplex c₁]
    | .Single x₁ d₁, .Single x₂ d₂ =>
      [.Single (.Prod x₁ x₂) (d₁ + d₂)]
    | .Single x₁ d₁, .Pair x₂ y₂ d₂ η₂ =>
      [.Pair (.Prod x₁ x₂) (.Prod x₁ y₂)
       (d₁ + d₂) (((-1)^d₁ : Int) * η₂)]
    | .Pair x₁ y₁ d₁ η₁, .Single x₂ d₂ =>
      [.Pair (.Prod x₁ x₂) (.Prod y₁ x₂) (d₁ + d₂) η₁]
    | .Pair x₁ y₁ d₁ η₁, .Pair x₂ y₂ d₂ η₂ =>
      [.Pair (.Prod x₁ x₂) (.κ x₁ y₁ x₂ y₂) (d₁ + d₂) (gcd η₁ η₂),
       .Pair (.τ x₁ y₁ x₂ y₂) (.Prod y₁ y₂) (d₁ + d₂ + 1) (gcd η₁ η₂)]

def tensorAtomicComplexes
  (maxDeg : Nat)
  (Cs : List (List (AtomicComplex Γ R)))
  : List (AtomicComplex (TPGenerator Γ) R) :=
  Cs.foldr (tensor₂AtomicComplexes maxDeg) [.One]
