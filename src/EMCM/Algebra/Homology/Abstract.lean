-- TODO document

import EMCM.Algebra.FgAb
import EMCM.Notation

namespace EMCM.Algebra.Homology.Abstract
open FgAb Notation

abbrev Homology := Array FgAb

abbrev Cohomology := Homology

namespace Homology

def directSum : Homology → Homology → Homology :=
  .zipWith (· ⊕ ·)

instance : Oplus Homology where
  oplus := .directSum

/-- Given H(A) H(B), compute H(A ⊗ B) according to the Künneth formula.
    A and B must have the same length; the output will have this length as well
    (cutting of H(A ⊗ B) in higher degree; pad the input with zeros to access these). -/
def künneth₂ (HA HB : Homology) : Homology :=
  .ofFn (n := HA.size) λ n =>
    let n := n.toNat
    let tensorTerm : FgAb := (0...=n).toArray
      |>.map (λ i => HA[i]! ⊗ HB[n - i]!)
      |>.foldl (· ⊕ ·) 0
    let torTerm : FgAb := (0...=n - 1).toArray
      |>.map (λ i => tor HA[i]! HB[n - i - 1]!)
      |>.foldl (· ⊕ ·) 0
    tensorTerm ⊕ torTerm

def künneth (Hs : List Homology) (maxDeg : Option Nat := none)
  : Homology :=
  let size :=
    maxDeg.map (· + 1) |>.getD
    <| Hs.map (·.size) |>.max?.getD 1
  Hs.map (·.rightpad size 0)
    |>.foldl künneth₂ (Array.replicate size 0 |>.set! 0 ℤ)

/-- Given H_*(X; ℤ), compute H_*(X; A) using the Universal Coefficient Theorem. -/
def homologyUCT (H : Homology) (A : FgAb) : Homology :=
  .ofFn (n := H.size) λ | ⟨0, _⟩ => H[0]! ⊗ A
                        | ⟨n, _⟩ => H[n]! ⊗ A ⊕ tor H[n-1]! A

/-- Given H_*(X; ℤ), compute H^*(X; A) using the Universal Coefficient Theorem. -/
def cohomologyUCT (H : Homology) (A : FgAb) : Cohomology :=
  .ofFn (n := H.size) λ | ⟨0, _⟩ => hom H[0]! A
                        | ⟨n, _⟩ => ext H[n-1]! A ⊕ hom H[n]! A

def print (H : Homology)
  (name : Option String := none)
  (coeffName : Option String := none)
  (range : Option (Std.Rcc Nat) := none)
  (extra : Nat → FgAb → IO Unit := λ _ _ => pure ())
  (displayℤAs : String := "ℤ")
  (cohomology : Bool := false)
  : IO Unit :=
  let argument := match name, coeffName with
    | none, none => ""
    | some G, none => s!"({G})"
    | none, some A => s!"(─; {A})"
    | some G, some A => s!"({G}; {A})"
  let range := range.getD (0...=H.size - 1)
  let sscript :=
    if cohomology then Nat.superscript else Nat.subscript
  for i in range do
    println! s!"H{sscript i}{argument} ≅ {H[i]!.displayℤAs displayℤAs}"
    extra i H[i]!

end Homology

namespace Cohomology

def print
  (H : Cohomology)
  (name : Option String := none)
  (coeffName : Option String := none)
  (range : Option (Std.Rcc Nat) := none)
  (extra : Nat → FgAb → IO Unit := λ _ _ => pure ())
  (displayℤAs : String := "ℤ")
  : IO Unit :=
  Homology.print H name coeffName range extra displayℤAs true

end Cohomology
