import EMCM.ElementaryComplex.Basic
import EMCM.ElementaryComplex.AtomicComplexes
import EMCM.Algebra.ChainComplex.TensorProduct
import EMCM.Algebra.FgAb
import EMCM.Algebra.Homology.Abstract
import EMCM.Algebra.Homology.Generated
import EMCM.Algebra.Structures
import EMCM.Algebra.PLocal

import Init.Data.List

namespace EMCM
open ElementaryComplex
open Algebra FgAb Homology Abstract Homology Structures

def BhGName (h : Nat) (G : FgAb) : String :=
  let sh := if h == 1 then "" else h.superscript
  let sG := toString G
  s!"B{sh}" ++ if sG.contains ' ' then s!"({sG})" else sG

def BhGLaTexName (h : Nat) (G : FgAb) : String :=
  let sh := if h == 1 then "" else s!"^\{{h}}"
  let lG := latex G
  s!"B{sh}" ++ if (toString G).contains ' '
  then s!"({lG})" else lG

/-- The homology H_*(BʰG; ℤ). -/
def BhGHomologyℤ
  (maxDeg : Nat) (h : Nat) (G : FgAb) : Homology :=
  let ECs := deloopGUpToDegree (discardUnits := true)
                               maxDeg h G (R := Int)
  künneth (maxDeg := maxDeg) <|
    ECs.map λ EC =>
      EC.atomicComplexes maxDeg
      |>.flatMap (·.ringChange (R' := pLocal EC.prime) id)
      |> HomologyComplex.ofAtomic (maxDeg := maxDeg)
      |>.toAbstract

/-- The homology H_*(BʰG; A). -/
def BhGHomology
  (maxDeg : Nat) (h : Nat) (G A : FgAb) : Homology :=
  homologyUCT (BhGHomologyℤ maxDeg h G) A

/-- The cohomology H^*(BʰG; A). -/
def BhGCohomology
  (maxDeg : Nat) (h : Nat) (G A : FgAb) : Cohomology :=
  cohomologyUCT (BhGHomologyℤ maxDeg h G) A

namespace ElementaryComplex
abbrev HomologyGenerator R [PrincipalRing R] :=
  Homology.Generator ElementaryComplex.Generator R

abbrev CohomologyGenerator R [PrincipalRing R] :=
  Cohomology.Generator ElementaryComplex.Generator R

end ElementaryComplex

open ChainComplex TensorProduct

abbrev BhGHomologyGenerator R [PrincipalRing R] :=
  Homology.Generator (TPGenerator ElementaryComplex.Generator) R

abbrev BhGCohomologyGenerator R [PrincipalRing R] :=
  Cohomology.Generator (TPGenerator ElementaryComplex.Generator) R

abbrev BhGℝℤCohomologyGenerator :=
  Cohomology.ℝℤGenerator (TPGenerator ElementaryComplex.Generator)

abbrev BhGHomologyComplex R [PrincipalRing R] :=
  HomologyComplex (TPGenerator ElementaryComplex.Generator) R

abbrev BhGCohomologyComplex R [PrincipalRing R] :=
  CohomologyComplex (TPGenerator ElementaryComplex.Generator) R

variable [PrincipalRing R]

def homologyComplexOfECs
  (maxDeg : Nat)
  (ECs : List (ElementaryComplex R))
  : BhGHomologyComplex R :=
  ECs.map (λ EC => EC.atomicComplexes maxDeg (discardUnits := true))
  |> tensorAtomicComplexes maxDeg
  |> HomologyComplex.ofAtomic (maxDeg := maxDeg)

def cohomologyComplexOfECs
  (maxDeg : Nat)
  (ECs : List (ElementaryComplex R))
  : BhGHomologyComplex R :=
  ECs.map (λ EC => EC.atomicComplexes maxDeg (discardUnits := true))
  |> tensorAtomicComplexes maxDeg
  |> CohomologyComplex.ofAtomic (maxDeg := maxDeg)

def BhGHomology'
  (maxDeg : Nat) (h : Nat) (G : FgAb) : BhGHomologyComplex R :=
  homologyComplexOfECs maxDeg (deloopGUpToDegree maxDeg h G)

def BhGCohomology'
  (maxDeg : Nat) (h : Nat) (G : FgAb) : BhGCohomologyComplex R :=
  cohomologyComplexOfECs maxDeg (deloopGUpToDegree maxDeg h G)
