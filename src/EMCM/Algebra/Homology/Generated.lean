-- TODO document

import EMCM.Algebra.ChainComplex.AtomicComplex
import EMCM.Algebra.Homology.Abstract
import EMCM.Algebra.ScalarMultiple
import EMCM.Notation
import EMCM.Util.LaTeX

namespace EMCM.Algebra
open Structures Ring PrincipalRing ChainComplex
open Notation FgAb Homology.Abstract

variable {Γ : Type u₁} {R : Type u₂} [PrincipalRing R]



namespace Homology
  /-- A (scalar multiple of) a homology generator. -/
  inductive Generator Γ R [PrincipalRing R] where
    | Scalar (r : R)
    | Gen (g : ScalarMultiple Γ R) (degree : Nat) (order : Order)
    deriving Inhabited, BEq

  instance : Zero (Generator Γ R) where
    zero := .Scalar 0

  instance : One (Generator Γ R) where
    one := .Scalar 1

  instance [ToString Γ] [ToString R] : ToString (Generator Γ R) where
    toString | .Scalar r => toString r
             | .Gen g _ o => s!"{g}⟨{o}⟩"

  instance [LaTeX Γ] [LaTeX R] : LaTeX (Generator Γ R) where
    latex | .Scalar r => latex r
          | .Gen g _ o => s!"{latex g}\\langle {latex o} \\rangle"

  def Generator.degree : Generator Γ R → Nat
    | .Scalar _ => 0
    | .Gen _ d _ => d

  def Generator.order : Generator Γ R → Order
    | .Scalar r => let c := characteristic R
                   c.toNat / gcd ↑c r
    | .Gen _ _ o => o

  instance : SMul R (Generator Γ R) where
    smul k | .Scalar r => .Scalar (k * r)
           | .Gen g d o =>
             let o' : Order := o.toNat / gcd k o
             if o' == 1 then 0
             else .Gen (k • g) d o'

  def Generator.ofAtomic
    : AtomicComplex Γ R → List (Generator Γ R)
    | .One => [1]
    | .Single x d => [.Gen x d (characteristic R)]
    | .Pair x y d η =>
      (let c := characteristic R
       let g := gcd η c
       .Gen x d g :: if c.isFinite
                     then [.Gen ((c.toNat / g : R) • y) (d + 1) g]
                     else [])
      |>.filter (·.order != 1)
end Homology

abbrev HomologyComplex (Γ : Type u₁) (R : Type u₂) [PrincipalRing R] :=
  Array (Array (Homology.Generator Γ R))

def HomologyComplex.ofGenerators
  (gens : List (Homology.Generator Γ R))
  (maxDeg : Option Nat := none)
  : HomologyComplex Γ R :=
  if let some maxDeg := maxDeg <|> (gens.map (·.degree) |>.max?)
  then
    gens.foldl (init := .replicate (maxDeg + 1) .empty)
    λ acc c =>
      if c.degree ≤ maxDeg
      then acc.modify c.degree (·.push c)
      else acc
  else #[#[1]]

def HomologyComplex.ofAtomic
  (ACs : List (AtomicComplex Γ R))
  (maxDeg : Option Nat := none)
  : HomologyComplex Γ R :=
  ACs.flatMap Homology.Generator.ofAtomic
  |> .ofGenerators (maxDeg := maxDeg)

def HomologyComplex.toAbstract
  (HC : HomologyComplex Γ R) : Homology :=
  HC.map λ gens => gens.foldl (· ⊕ ℤN ·.order) 0

namespace Cohomology
  def Generator Γ := Homology.Generator Γ

  instance : Inhabited (Generator Γ R) :=
    by unfold Generator; infer_instance
  instance [BEq Γ] [BEq R] : BEq (Generator Γ R) :=
    by unfold Generator; infer_instance
  instance : Zero (Generator Γ R) :=
    by unfold Generator; infer_instance
  instance : One (Generator Γ R) :=
    by unfold Generator; infer_instance
  instance : SMul R (Generator Γ R) :=
    by unfold Generator; infer_instance

  instance [ToString Γ] [ToString R]
    : ToString (Generator Γ R) where
    toString | .Scalar r => toString r
             | .Gen (.Mul c g) _ o =>
               toString (α := ScalarMultiple String R) (c • s!"({g})*")
               ++ s!"⟨{o}⟩"
             | .Gen .Zero _ _ => unreachable!

  instance [LaTeX Γ] [LaTeX R]
    : LaTeX (Generator Γ R) where
    latex | .Scalar r => latex r
          | .Gen (.Mul c g) _ o =>
            latex (α := ScalarMultiple String R) (c • s!"({latex g})^*")
            ++ s!"\\langle {latex o} \\rangle"
          | .Gen .Zero _ _ => unreachable!

  def Generator.degree : Generator Γ R → Nat :=
    Homology.Generator.degree

  def Generator.order : Generator Γ R → Order :=
    Homology.Generator.order

  def Generator.ofAtomic [PrincipalRing R]
  : AtomicComplex Γ R → List (Generator Γ R)
    | .One => [1]
    | .Single x d => [.Gen x d (characteristic R)]
    | .Pair x y d η =>
      (let c := characteristic R
       let g := gcd η c
       .Gen y (d + 1) g :: if c.isFinite
                           then [.Gen ((c.toNat / g : R) • x) d g]
                           else [])
      |>.filter (·.order != 1)

  abbrev ℝℤGenerator Γ := Homology.Generator Γ Int

  instance [ToString Γ] : ToString (ℝℤGenerator Γ) :=
    inferInstanceAs <| ToString (Cohomology.Generator Γ Int)

  instance [LaTeX Γ] : LaTeX (ℝℤGenerator Γ) :=
    inferInstanceAs <| LaTeX (Cohomology.Generator Γ Int)
end Cohomology

abbrev CohomologyComplex (Γ : Type u₁) (R : Type u₂) [PrincipalRing R] :=
  Array (Array (Cohomology.Generator Γ R))

def CohomologyComplex.ofAtomic
  (ACs : List (AtomicComplex Γ R))
  (maxDeg : Option Nat := none)
  : CohomologyComplex Γ R :=
  ACs.flatMap Cohomology.Generator.ofAtomic
  |> HomologyComplex.ofGenerators (maxDeg := maxDeg)

def CohomologyComplex.toAbstract
  : (CC : CohomologyComplex Γ R) → Cohomology :=
  HomologyComplex.toAbstract

abbrev ℝℤCohomologyComplex (Γ : Type u₁) :=
  Array (Array (Cohomology.ℝℤGenerator Γ))

def ℝℤCohomologyComplex.toAbstract
  : (CC : ℝℤCohomologyComplex Γ) → Cohomology :=
  HomologyComplex.toAbstract
