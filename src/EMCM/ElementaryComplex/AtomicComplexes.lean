import EMCM.Algebra.ChainComplex.AtomicComplex
import EMCM.Algebra.Structures
import EMCM.ElementaryComplex.Basic

namespace EMCM.ElementaryComplex
open Algebra Structures ChainComplex PrincipalRing

/-- A single word or a product of two words from a single
elementary complex, together with the path labelling that complex. -/
inductive Generator where
  /-- A single word. -/
  | Word (P : Path) (w : Word)
  /-- A product of two words. -/
  | Product (P : Path) (w₁ w₂ : Word)
  deriving Inhabited, BEq, Hashable

instance : ToString Generator where
  -- toString does not display the path
  toString | .Word _ w => s!"{w}"
           | .Product _ w₁ w₂ => s!"{w₁}·{w₂}"

instance (priority := low) : ToString Generator where
  toString | .Word P w => s!"[{P}]{w}"
           | .Product P w₁ w₂ => s!"[{P}]{w₁}·{w₂}"

instance : LaTeX Generator where
  -- toString does not display the path
  latex | .Word _ w => s!"{latex w}"
        | .Product _ w₁ w₂ => s!"{latex w₁} \\cdot {latex w₂}"

def Generator.path : Generator → Path
  | .Word P .. | .Product P .. => P

-- TODO tryDecompose unneccesary? Already done on the complexes.
/-- All the atomic complexes over the ring R in an elementary complex. -/
def atomicComplexes [PrincipalRing R]
  (maxDeg : Nat) (discardUnits : Bool := false)
  : ElementaryComplex R → List (AtomicComplex Generator R)
  | .Λℤ P _ a => [.One, .Single (.Word P a) 0]
  | .ΛℤN P _ _ u => [.One, .Single (.Word P u) 0]
  | .AI P _ x n => [.One, .Single (.Word P x) n]
  | .BI P _ x n =>
    .One :: (
      (1...*).iter
      |>.map (λ k => .Single (.Word P (.γ k x)) (k * n))
      |>.takeWhile (·.degree ≤ maxDeg)
      |>.toList)
  | .AII P p x y n η =>
    (.One :: .Pair (.Word P x) (.Word P y) n (loc p η) :: (
      (1...*).iter
      |>.map (λ k => AtomicComplex.Pair
                     (.Product P x (.γ k y)) (.Word P (.γ (k + 1) y))
                     (n + k * (n + 1)) (loc p η))
      |>.takeWhile (·.degree ≤ maxDeg)
      |>.toList)
    |>.flatMap (·.tryDecompose))
  | .BII P p x y n η =>
    (.One :: .Pair (.Word P x) (.Word P y) n (loc p η) :: (
      (2...*).iter
      |>.map (λ k => AtomicComplex.Pair
                     (.Word P (.γ k x)) (.Product P (.γ (k - 1) x) y)
                     (k * n) (loc p (η * k)))
      |>.takeWhile (·.degree ≤ maxDeg)
      |>.toList)
    |>.flatMap (·.tryDecompose))
  where loc (p : Nat) (η : R) : R :=
    if discardUnits then
      let η := toInt η
      η.sign * η.natAbs.primeComponent p
    else η
