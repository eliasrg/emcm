import EMCM.Util.LaTeX
import EMCM.Util.Prime
import EMCM.Util.Script

namespace EMCM.Algebra

/-- Isomorphism class of a finitely generated abelian group,
    without information about its generators. -/
structure FgAb where
  rank : Nat
  /-- [(prime, [(power, multiplicity)])]
      (sorted, with each prime and power occurring only once) -/
  torsion : List (Nat × List (Nat × Nat))
  deriving Repr, Inhabited, BEq

namespace FgAb

/-- Merge occurrences of the same prime or prime power.
    Delete groups to the power 0.
    Delete primes with no power. -/
def normalize : FgAb → FgAb
  | ⟨rank, torsion⟩ => .mk rank <|
    torsion.filter (¬·.2.isEmpty)
    |>.mergeSort (·.1 ≤ ·.1)
    |>.splitBy (λ (p, _) (p', _) => p == p')
    |>.map λ | [] => unreachable!
             | pfms@((p,_) :: _) =>
               let fms := pfms.flatMap (·.2)
                 |>.filter (λ (_, m) => m != 0)
                 |>.mergeSort (·.1 ≤ ·.1)
                 |>.splitBy (λ (f, _) (f', _) => f == f')
                 |>.map λ | [] => unreachable!
                          | fms@((f, _) :: _) =>
                            (f, fms.map (·.2) |>.sum)
               (p, fms)

def torsionFactors : FgAb → List (Nat × Nat)
  | ⟨_, torsion⟩ =>
    torsion.flatMap (λ (p, fms) => fms.map λ (f, m) => (p^f, m))
    |>.mergeSort λ | (p₁, _), (p₂, _) => p₁ ≤ p₂

def toStringWithℤAs (s : String) : FgAb → String
  | ⟨0, []⟩ => "0"
  | ⟨1, []⟩ => s
  | ⟨rank, []⟩ => s!"{s}{rank.superscript}"
  | G@⟨0, _⟩ =>
    " ⊕ ".intercalate <|
    G.torsionFactors.map λ (pf, m) =>
      let ℤpf := s!"ℤ{(pf).subscript}"
      if m == 1 then ℤpf else s!"({ℤpf}){m.superscript}"
  | ⟨rank@(_ + 1), torsion@(_ :: _)⟩ =>
    s!"{toStringWithℤAs s ⟨rank, []⟩} ⊕ {toStringWithℤAs s ⟨0, torsion⟩}"
  termination_by G => G.rank + G.torsion.length

instance : ToString FgAb where
  toString := toStringWithℤAs "ℤ"

def toLaTeXWithℤAs (s : String) : FgAb → String
  | ⟨0, []⟩ => "0"
  | ⟨1, []⟩ => s
  | ⟨rank, []⟩ => s!"{s}^\{{rank}}"
  | G@⟨0, _⟩ =>
    " \\oplus ".intercalate <|
    G.torsionFactors.map λ (pf, m) =>
      let ℤpf := s!"\\mathbb\{Z}_\{{pf}}"
      if m == 1 then ℤpf else s!"({ℤpf})^\{{m}}"
  | ⟨rank@(_ + 1), torsion@(_ :: _)⟩ =>
    s!"{toLaTeXWithℤAs s ⟨rank, []⟩} \\oplus {toLaTeXWithℤAs s ⟨0, torsion⟩}"
  termination_by G => G.rank + G.torsion.length

instance : LaTeX FgAb where
  latex := toLaTeXWithℤAs "\\mathbb{Z}"

instance : Zero FgAb where
  zero := { rank := 0, torsion := [] }

def ℤ : FgAb := { rank := 1, torsion := [] }
def ℤN (N : Nat) : FgAb :=
  if N == 0 then ℤ
  else { rank := 0, torsion := N.factor.map λ (p, f) => (p, [(f, 1)]) }

def isFinite : FgAb → Bool := (·.rank == 0)

def freePart : FgAb → FgAb
  | ⟨rank, _⟩ => ⟨rank, []⟩

def torsionPart : FgAb → FgAb
  | ⟨_, torsion⟩ => ⟨0, torsion⟩

def removeTorsionOtherThan (p : Nat) : FgAb → FgAb
  | ⟨rank, torsion⟩ => ⟨rank, torsion.filter (·.1 == p)⟩
