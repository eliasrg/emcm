import EMCM
import EMCMCli.Common
import EMCMCli.LaTeX
import Cli

import Std.Data.HashMap

open EMCMCli
open EMCM
open Algebra ZMod FgAb Structures Homology
open ChainComplex TensorProduct
open ElementaryComplex
open Cli
open Std

def runHomologyGenerators
  (maxDeg : Nat)
  (h : Nat) (G : FgAb) (RArg : CoeffRing)
  (suspension : Bool)
  (onlyNonzero : Bool := false)
  : IO Unit := do
    let R := RArg.ring
    let RName := toString RArg

    let ECs := deloopGUpToDegree (R := R) maxDeg h G
    let H := homologyComplexOfECs maxDeg ECs

    let ECsMap : HashMap Path (ElementaryComplex R) :=
      .ofList <| ECs.map λ EC => (EC.path, EC)

    if suspension then
      println! "σ: Hₙ({BhGName h G}; {RName}) → Hₙ₊₁({BhGName (h+1) G}; {RName})"
    H.toAbstract
    |>.print
      (name := BhGName h G) (coeffName := RName) (displayℤAs := RName)
      (extra := λ i _ => do
        let Hi := H[i]!
        Hi.forM λ g => do
          if !suspension then
            println! "        {g}"
          else
            let σg := suspend ECsMap g
            if σg == 0 then
              if !onlyNonzero then println! "        {g}"
            else
              println! "     σ: {g} ↦ {σg}")

def runCohomologyGenerators
  (maxDeg : Nat)
  (h : Nat) (G : FgAb) (AArg : RingOrCircle)
  (cosuspension : Bool)
  (onlyNonzero : Bool := false)
  : IO Unit := do
    let AName := toString AArg
    match AArg with
    | .Circle _ =>
      let H : ℝℤCohomologyComplex _ := BhGHomology' (R := Int) maxDeg h G

      let lowerECs := deloopGUpToDegree (R := Int) maxDeg (h - 1) G
      let lowerHomology := homologyComplexOfECs maxDeg lowerECs
      let cosuspendℝℤ' := cosuspendℝℤ
        (.ofList <| lowerECs.map λ EC => (EC.path, EC))
        lowerHomology

      if cosuspension then
        assert! h > 0
        println! "Ω: Hⁿ⁺¹({BhGName h G}; {AName}) → Hⁿ({BhGName (h - 1) G}; {AName})"
      H.toAbstract.print
        (name := BhGName h G) (coeffName := AName) (displayℤAs := AName)
        (extra := λ i _ => do
          let Hi := H[i]!
          Hi.forM λ g => do
            if !cosuspension then
              println! "        {g}"
            else
              let Ωg := cosuspendℝℤ' g
              if Ωg == 0 then
                if !onlyNonzero then println! "        {g}"
              else
                println! "     Ω: {g} ↦ {Ωg}")

    | .Ring RArg =>
      let R := RArg.ring
      let H := BhGCohomology' (R := R) maxDeg h G

      let lowerECs : HashMap Path (ElementaryComplex R) :=
        .ofList <|
        deloopGUpToDegree (R := R) maxDeg (h - 1) G
        |>.map λ EC => (EC.path, EC)

      if cosuspension then
        assert! h > 0
        println! "Ω: Hⁿ⁺¹({BhGName h G}; {AName}) → Hⁿ({BhGName (h - 1) G}; {AName})"
      H.toAbstract.print
        (name := BhGName h G) (coeffName := AName) (displayℤAs := AName)
        (extra := λ i _ => do
          let Hi := H[i]!
          Hi.forM λ g => do
            if !cosuspension then
              println! "        {g}"
            else
              let Ωg := cosuspend lowerECs g
              if Ωg == 0 then
                if !onlyNonzero then println! "        {g}"
              else
                println! "     Ω: {g} ↦ {Ωg}")


section Cli
  def homology := `[Cli|
    homology VIA run;
    "Compute the homology groups Hₙ(BʰG; A)."

    FLAGS:
      d, maxdeg : Nat; "Compute homology up to this degree."

    ARGS:
      h : Nat; "The number of deloopings to apply."
      G : FgAb; FgAbDocstring
      A : FgAbOrLocal; docstring

    EXTENSIONS:
      defaultValues! #[("maxdeg", "20")];
      longDescription "This command uses the Universal Coefficient theorem to \
        compute high-dimensional homology groups efficiently, without enumerating \
        all the generators like homology-gens does."
    ]
  where
  docstring := s!"The abelian group of coefficients. {FgAbOrLocalDocstring}"
  run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let h := p.positionalArg! "h" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let A := p.positionalArg! "A" |>.as! FgAbOrLocal

    match A with
    | .FgAb A =>
      BhGHomology maxDeg h G A
      |>.print (name := BhGName h G) (coeffName := toString A)
    | .Local (.Local p) =>
      BhGHomology maxDeg h G ℤ
      |>.map (·.removeTorsionOtherThan p)
      |> Abstract.Homology.print (name := BhGName h G) (coeffName := toString A)
                                 (displayℤAs := toString A)

    return 0

  def cohomology := `[Cli|
    cohomology VIA run;
    "Compute the cohomology groups Hⁿ(BʰG; A)."

    FLAGS:
      d, maxdeg : Nat; "Compute cohomology up to this degree."

    ARGS:
      h : Nat; "The number of deloopings to apply."
      G : FgAb; FgAbDocstring
      A : FgAbOrLocalOrCircle; docstring

    EXTENSIONS:
      defaultValues! #[("maxdeg", "20")];
      longDescription "This command uses the Universal Coefficient theorem to \
        compute high-dimensional cohomology groups efficiently, without enumerating \
        all the generators like cohomology-gens does."
    ]
  where
  docstring := s!"The abelian group of coefficients. {FgAbOrLocalOrCircleDocstring}"
  run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let h := p.positionalArg! "h" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let A := p.positionalArg! "A" |>.as! FgAbOrLocalOrCircle

    match A with
    | .FgAb A =>
      BhGCohomology maxDeg h G A
      |>.print (name := BhGName h G) (coeffName := toString A)
    | .Local (.Local p) =>
      BhGCohomology maxDeg h G ℤ
      |>.map (·.removeTorsionOtherThan p)
      |> Abstract.Cohomology.print (name := BhGName h G) (coeffName := toString A)
                                   (displayℤAs := toString A)
    | .Circle _ =>
      BhGHomology maxDeg h G ℤ
      |>.print (name := BhGName h G) (coeffName := toString A)
               (displayℤAs := toString A)

    return 0

  def «homology-gens» := `[Cli|
    "homology-gens" VIA run;
    "List the generators of the homology groups Hₙ(BʰG; R)."

    FLAGS:
      d, maxdeg : Nat; "Compute homology up to this degree."

    ARGS:
      h : Nat; "The number of deloopings to apply."
      G : FgAb; FgAbDocstring
      R : CoeffRing; CoeffRingDocstring

    EXTENSIONS:
      defaultValues! #[("maxdeg", "20")]
    ]
  where run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let h := p.positionalArg! "h" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let RArg := p.positionalArg! "R" |>.as! CoeffRing

    runHomologyGenerators maxDeg h G RArg (suspension := false)

    return 0

  def «cohomology-gens» := `[Cli|
    "cohomology-gens" VIA run;
    "List the generators of the cohomology groups Hⁿ(BʰG; A)."

    FLAGS:
      d, maxdeg : Nat; "Compute cohomology up to this degree."

    ARGS:
      h : Nat; "The number of deloopings to apply."
      G : FgAb; FgAbDocstring
      A : RingOrCircle; RingOrCircleDocstring

    EXTENSIONS:
      defaultValues! #[("maxdeg", "20")]
    ]
  where run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let h := p.positionalArg! "h" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let AArg := p.positionalArg! "A" |>.as! RingOrCircle

    runCohomologyGenerators maxDeg h G AArg (cosuspension := false)

    return 0

  def suspension := `[Cli|
    suspension VIA run;
    "Compute the suspension σ: Hₙ(BʰG; R) → Hₙ₊₁(Bʰ⁺¹G; R)."

    FLAGS:
      d, maxdeg : Nat; "Compute homology up to this degree."
      s, skip; "Do not print generators with zero suspension."

    ARGS:
      h : Nat; "The number of deloopings to apply."
      G : FgAb; FgAbDocstring
      R : CoeffRing; CoeffRingDocstring

    EXTENSIONS:
      defaultValues! #[("maxdeg", "20")]
    ]
  where run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let skip := p.hasFlag "skip"
    let h := p.positionalArg! "h" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let RArg := p.positionalArg! "R" |>.as! CoeffRing

    runHomologyGenerators maxDeg h G RArg
      (suspension := true) (onlyNonzero := skip)

    return 0

  def cosuspension := `[Cli|
    cosuspension VIA run;
    "Compute the cosuspension (loop functor) Ω: Hⁿ⁺¹(Bʰ⁺¹G; A) → Hⁿ(BʰG; A)."

    FLAGS:
      d, maxdeg : Nat; "Compute cohomology up to this degree."
      s, skip; "Do not print generators with zero cosuspension."

    ARGS:
      h : PosNat; "The number of deloopings to apply."
      G : FgAb; FgAbDocstring
      A : RingOrCircle; RingOrCircleDocstring

    EXTENSIONS:
      defaultValues! #[("maxdeg", "20")]
    ]
  where run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let skip := p.hasFlag "skip"
    let h := p.positionalArg! "h" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let AArg := p.positionalArg! "A" |>.as! RingOrCircle

    runCohomologyGenerators maxDeg h G AArg
      (cosuspension := true) (onlyNonzero := skip)

    return 0

  def elementary := `[Cli|
    elementary VIA run;
    "List the elementary complexes appearing in BʰG."

    FLAGS:
      d, maxdeg : Nat; "List the complexes up to this degree."
      p, paths; "Print describing how the complexes were constructed."
      u, unsorted; "Do not sort complexes by degree."

    ARGS:
      h : Nat; "The number of deloopings to apply."
      G : FgAb; FgAbDocstring
      R : CoeffRing; CoeffRingDocstring

    EXTENSIONS:
      defaultValues! #[("maxdeg", "100")]
    ]
  where run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let unsorted := p.hasFlag "unsorted"
    let paths := p.hasFlag "paths"
    let h := p.positionalArg! "h" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let RArg := p.positionalArg! "R" |>.as! CoeffRing
    let R := RArg.ring

    let mut ECs := deloopGUpToDegree (R := R) maxDeg h G
    if !unsorted then ECs := ECs.mergeSort (·.degree ≤ ·.degree)

    ECs.forM λ c => if paths
      then println! "{c.path}: {c}"
      else println! c

    return 0

  def atomic := `[Cli|
    atomic VIA run;
    "List the atomic complexes appearing in BʰG."

    FLAGS:
      d, maxdeg : Nat; "List the complexes up to this degree."
      u, unsorted; "Do not sort complexes by degree."

    ARGS:
      h : Nat; "The number of deloopings to apply."
      G : FgAb; FgAbDocstring
      R : CoeffRing; CoeffRingDocstring

    EXTENSIONS:
      defaultValues! #[("maxdeg", "20")]
    ]
  where run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let unsorted := p.hasFlag "unsorted"
    let h := p.positionalArg! "h" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let RArg := p.positionalArg! "R" |>.as! CoeffRing
    let R := RArg.ring

    let mut ECs := deloopGUpToDegree (R := R) maxDeg h G
    if !unsorted then ECs := ECs.mergeSort (·.degree ≤ ·.degree)

    let mut ACs := tensorAtomicComplexes maxDeg <| ECs.map (·.atomicComplexes maxDeg)
    if !unsorted then ACs := ACs.mergeSort (·.degree ≤ ·.degree)

    ACs.forM IO.println

    return 0

  def norm := `[Cli|
    norm VIA run;
    "Print the normalised form of a finitely generated abelian group."

    ARGS:
      G : FgAb; FgAbDocstring
    ]
  where run p := do
    let G := p.positionalArg! "G" |>.as! FgAb
    println! G
    return 0

  def mainCmd := `[Cli|
    emcm VIA run;
    "Compute (co)homology and suspension maps of \
    Eilenberg-MacLane spaces."

    SUBCOMMANDS:
      homology;
      cohomology;
      «homology-gens»;
      «cohomology-gens»;
      suspension;
      cosuspension;
      elementary;
      atomic;
      norm;
      latex

    EXTENSIONS:
      author "Elias Riedel Gårding";
      longDescription
"emcm (\"Eilenberg-MacLane-Cartan-Moore\") performs (co)homology \
computations for Eilenberg-MacLane spaces for finitely generated \
abelian groups using Cartan's notion of construction and Moore's \
constructions over the ring of integers localised at a prime."
    ]
  where run p := do
    p.printHelp
    return 0
end Cli

def main (args : List String) : IO UInt32 :=
  mainCmd.validate args
