import EMCMCli.Common

import EMCM
import Cli

import Init.Data.String

import Std.Data.HashMap

open EMCM
open Algebra ZMod FgAb Structures
open ChainComplex TensorProduct
open ElementaryComplex
open Cli
open Std

namespace EMCMCli.LaTeX

def FgAbTable
  (groups : Array (Array FgAb))
  (rowIndex columnIndex : String)
  (rowStart : Nat := 0)
  (columnStart : Nat := 1)
  (displayℤAs : String := r"\mathbb{Z}")
  : IO Unit := do
  let columns := groups.size
  println! "\\begin\{tabular}\{l|{String.ofList <| .replicate columns 'c'}}"
  println! s!"\\diagbox[width=4em]\{{rowIndex}}\{{columnIndex}} & "
    ++ " & ".intercalate (List.range' columnStart columns |>.map toString)
    ++ r" \\"
  println! "\\hline"
  groups.transpose.zipIdx.forM λ (row, i) => do
    println! s!"{rowStart + i} & "
      ++ (" & ".intercalate (row.toList.map (latexMath ∘ FgAb.displayℤAs displayℤAs)))
      ++ r" \\"
  println! "\\end\{tabular}"

def abstractSuspensionTable [BEq Γ] [PrincipalRing R]
  (Hs : Array (HomologyComplex Γ R))
  (suspensions : Array (Homology.Generator Γ R → Homology.Generator Γ R))
  (cohomology : Bool := false)
  (displayℤAs : String := r"\mathbb{Z}")
  (names : Nat → String)
  (rowStart : Nat := 0)
  (columnStart : Nat := 1)
  (rowsep : String := "tiny")
  (colsep : String := "tiny")
  : IO Unit := do
  let columns := Hs.size
  let rows := Hs[0]!.size
  let abstract := Hs.map (·.toAbstract)
  println! "\\begin\{tikzcd}[row sep={rowsep},column sep={colsep}]"
  println! ("& " ++ " & ".intercalate (List.range' columnStart columns |>.map names) ++ r" \\")
  Hs.zipWith Array.zip abstract |>.transpose.zipIdx.forM λ (row, i) =>
    let indexS := (if cohomology then "H^" else "H_") ++ s!"\{{rowStart + i}}"
    let rowS := " & ".intercalate <|
      row.toList.zipIdx.map λ ((Hi, Hia), j) =>
      latex (Hia.displayℤAs displayℤAs)
      ++ if !cohomology ∧ i + 1 < rows ∧ j + 1 < columns
           ∨ cohomology ∧ i > 0 ∧ j > 0
      then
        let n := (Hi.map suspensions[if cohomology then j - 1 else j]!).countP (· != 0)
        if n > 0
        then s!"\\ar[{if cohomology then s!"lu,\"{n}\"'" else s!"rd,\"{n}\""}]"
        else ""
      else ""
    println! s!"{indexS} & " ++ rowS ++ r" \\"
  println! r"\end{tikzcd}"

def generatorSuspensionTable
  [BEq Γ] [PrincipalRing R] [LaTeX (Homology.Generator Γ R)]
  (H : HomologyComplex Γ R)
  (suspend : Homology.Generator Γ R → Homology.Generator Γ R)
  (cohomology : Bool := false)
  (onlyNonzero : Bool := false)
  (omitAbstract : Bool := false)
  (name : Option String := none)
  (coeffName : Option String := none)
  (displayℤAs : String := r"\mathbb{Z}")
  (start : Nat := 0)
  : IO Unit := do
  let argument := match name, coeffName with
    | none, none => ""
    | some G, none => s!"({G})"
    | none, some A => s!"(─; {A})"
    | some G, some A => s!"({G}; {A})"
  let sscript :=
    if cohomology then "^" else "_"
  let Ha := H.toAbstract

  println! r"\begin{IEEEeqnarraybox}[][c]{rClrCl}"
  println! (r" \\" ++ "\n").intercalate <|
    (H.zip Ha).toList.zipIdx.drop start |>.flatMap λ ((Hi, Hia), i) =>
    let generatorLines := Hi.toList.filterMap λ g => do
      let σg := suspend g
      guard !(onlyNonzero ∧ σg == 0)
      return s!"{latex g} &\\longmapsto& {latex σg}"
    let abstractPart :=
      if omitAbstract then "&&"
      else s!"{latex (Hia.displayℤAs displayℤAs)} &\\cong&"
    let begin :=
      s!"{abstractPart} H{sscript}\{{i}}{argument} \\colon & "
    match generatorLines with
    | head :: tail => (begin ++ head) :: tail.map ("&&& " ++ ·)
    | [] => [begin]
  println! r"\end{IEEEeqnarraybox}"

def homology := `[Cli|
  homology VIA run;
  "Create a LaTeX table of the homology groups Hₙ(BʰG; A)."

  FLAGS:
    b, maxh : Nat; "The maximum number of deloopings to include."
    d, maxdeg : Nat; "Compute homology up to this degree."

  ARGS:
    G : FgAb; FgAbDocstring
    A : FgAbOrLocal; docstring

  EXTENSIONS:
    defaultValues! #[("maxh", "10"), ("maxdeg", "20")]
  ]
  where
  docstring := s!"The abelian group of coefficients. {FgAbOrLocalDocstring}"
  run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let maxH := p.flag! "maxh" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let A := p.positionalArg! "A" |>.as! FgAbOrLocal

    match A with
    | .FgAb A =>
      FgAbTable
        (.ofFn λ h : Fin maxH => BhGHomology maxDeg (h + 1) G A)
        "$h$" "$D$"
    | .Local (.Local p) =>
      FgAbTable
        (.ofFn λ h : Fin maxH => BhGHomology maxDeg (h + 1) G ℤ
                                 |>.map (·.removeTorsionOtherThan p))
        "$h$" "$D$"
        (displayℤAs := latex A)

    return 0

def cohomology := `[Cli|
  cohomology VIA run;
  "Create a LaTeX table of the cohomology groups Hⁿ(BʰG; A)."

  FLAGS:
    b, maxh : Nat; "The maximum number of deloopings to include."
    d, maxdeg : Nat; "Compute homology up to this degree."

  ARGS:
    G : FgAb; FgAbDocstring
    A : FgAbOrLocalOrCircle; docstring

  EXTENSIONS:
    defaultValues! #[("maxh", "10"), ("maxdeg", "20")]
  ]
  where
  docstring := s!"The abelian group of coefficients. {FgAbOrLocalOrCircleDocstring}"
  run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let maxH := p.flag! "maxh" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let A := p.positionalArg! "A" |>.as! FgAbOrLocalOrCircle

    match A with
    | .FgAb A =>
      FgAbTable
        (.ofFn λ h : Fin maxH => BhGCohomology maxDeg (h + 1) G A)
        "$h$" "$D$"
    | .Local (.Local p) =>
      FgAbTable
        (.ofFn λ h : Fin maxH => BhGCohomology maxDeg (h + 1) G ℤ
                                 |>.map (·.removeTorsionOtherThan p))
        "$h$" "$D$"
        (displayℤAs := latex A)
    | .Circle _ =>
      FgAbTable
        (.ofFn λ h : Fin maxH => BhGHomology maxDeg (h + 1) G ℤ)
        "$h$" "$D$"
        (displayℤAs := latex A)

    return 0

def suspension := `[Cli|
  suspension VIA run;
  "Tabulate the suspension σ: Hₙ(BʰG; R) → Hₙ₊₁(Bʰ⁺¹G; R) on generators."

  FLAGS:
    f, mindeg : Nat; "Compute homology starting in this degree."
    d, maxdeg : Nat; "Compute homology up to this degree."
    s, skip; "Do not print generators with zero suspension."
    n, "omit-abstract"; "Do not print the isomorphism classes of the homology groups."

  ARGS:
    h : Nat; "The number of deloopings to apply."
    G : FgAb; FgAbDocstring
    R : CoeffRing; CoeffRingDocstring

  EXTENSIONS:
    defaultValues! #[("mindeg", "0"), ("maxdeg", "20")]
  ]
  where run p := do
    let minDeg := p.flag! "mindeg" |>.as! Nat
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let skip := p.hasFlag "skip"
    let omitAbstract := p.hasFlag "omit-abstract"
    let h := p.positionalArg! "h" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let RArg := p.positionalArg! "R" |>.as! CoeffRing
    let R := RArg.ring
    let RName := latex RArg

    let ECs := deloopGUpToDegree (R := R) maxDeg h G
    let H := homologyComplexOfECs maxDeg ECs

    let ECsMap : HashMap Path (ElementaryComplex R) :=
      .ofList <| ECs.map λ EC => (EC.path, EC)

    generatorSuspensionTable H (suspend ECsMap)
      (cohomology := false)
      (onlyNonzero := skip)
      (omitAbstract := omitAbstract)
      (name := BhGLaTexName h G)
      (coeffName := RName)
      (displayℤAs := RName)
      (start := minDeg)

    return 0

def cosuspension := `[Cli|
  cosuspension VIA run;
  "Tabulate the cosuspension (loop functor) Ω: Hⁿ⁺¹(Bʰ⁺¹G; A) → Hⁿ(BʰG; A) on generators."

  FLAGS:
    f, mindeg : Nat; "Compute cohomology starting in this degree."
    d, maxdeg : Nat; "Compute cohomology up to this degree."
    s, skip; "Do not print generators with zero cosuspension."
    n, "omit-abstract"; "Do not print the isomorphism classes of the cohomology groups."

  ARGS:
    h : PosNat; "The number of deloopings to apply."
    G : FgAb; FgAbDocstring
    A : RingOrCircle; RingOrCircleDocstring

  EXTENSIONS:
    defaultValues! #[("mindeg", "0"), ("maxdeg", "20")]
  ]
  where run p := do
    let minDeg := p.flag! "mindeg" |>.as! Nat
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let skip := p.hasFlag "skip"
    let omitAbstract := p.hasFlag "omit-abstract"
    let h := p.positionalArg! "h" |>.as! Nat
    let G := p.positionalArg! "G" |>.as! FgAb
    let AArg := p.positionalArg! "A" |>.as! RingOrCircle
    let AName := latex AArg

    match AArg with
    | .Circle _ =>
      let H : ℝℤCohomologyComplex _ := BhGHomology' (R := Int) maxDeg h G

      let lowerECs := deloopGUpToDegree (R := Int) maxDeg (h - 1) G
      let lowerHomology := homologyComplexOfECs maxDeg lowerECs
      let cosuspendℝℤ' := cosuspendℝℤ
        (.ofList <| lowerECs.map λ EC => (EC.path, EC))
        lowerHomology

      generatorSuspensionTable H cosuspendℝℤ'
        (cohomology := true)
        (onlyNonzero := skip)
        (omitAbstract := omitAbstract)
        (name := BhGLaTexName h G)
        (coeffName := AName)
        (displayℤAs := AName)
        (start := minDeg)

    | .Ring RArg =>
      let R := RArg.ring
      let H := BhGCohomology' (R := R) maxDeg h G

      let lowerECs : HashMap Path (ElementaryComplex R) :=
        .ofList <|
        deloopGUpToDegree (R := R) maxDeg (h - 1) G
        |>.map λ EC => (EC.path, EC)

      generatorSuspensionTable H (cosuspend lowerECs)
        (cohomology := true)
        (onlyNonzero := skip)
        (name := BhGLaTexName h G)
        (coeffName := AName)
        (displayℤAs := AName)
        (start := minDeg)

    return 0

def «suspension-chart» := `[Cli|
  "suspension-chart" VIA run;
  "Tabulate the suspension σ: Hₙ(BʰG; R) → Hₙ₊₁(Bʰ⁺¹G; R) for a range of h."

  FLAGS:
    b, maxh : Nat; "The maximum number of deloopings to include."
    d, maxdeg : Nat; "Compute homology up to this degree."
    rowsep : String; "tikz-cd argument \"row sep\" for the table."
    colsep : String; "tikz-cd argument \"column sep\" for the table."

  ARGS:
    G : FgAb; FgAbDocstring
    R : CoeffRing; CoeffRingDocstring

  EXTENSIONS:
    defaultValues! #[("maxh", "10"), ("maxdeg", "20"), ("colsep", "tiny"), ("rowsep", "tiny")]
  ]
  where run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let maxH := p.flag! "maxh" |>.as! Nat
    let rowsep := p.flag! "rowsep" |>.as! String
    let colsep := p.flag! "colsep" |>.as! String
    let G := p.positionalArg! "G" |>.as! FgAb
    let RArg := p.positionalArg! "R" |>.as! CoeffRing
    let R := RArg.ring
    let RName := latex RArg

    let ECss := Array.ofFn
      (λ h : Fin maxH => deloopGUpToDegree (R := R) maxDeg (h + 1) G)
    let H := ECss.map (homologyComplexOfECs maxDeg)

    let ECsMaps : Array (HashMap Path (ElementaryComplex R)) :=
      ECss.map λ ECs => .ofList <| ECs.map λ EC => (EC.path, EC)
    let suspensions := ECsMaps.map suspend

    abstractSuspensionTable H suspensions
      (names := λ h => BhGLaTexName h G)
      (displayℤAs := RName)
      (rowsep := rowsep)
      (colsep := colsep)

    return 0

def «cosuspension-chart» := `[Cli|
  "cosuspension-chart" VIA run;
  "Tabulate the cosuspension (loop functor) \
Ω: Hⁿ⁺¹(Bʰ⁺¹G; A) → Hⁿ(BʰG; A) for a range of h."

  FLAGS:
    b, maxh : Nat; "The maximum number of deloopings to include."
    d, maxdeg : Nat; "Compute homology up to this degree."
    rowsep : String; "tikz-cd argument \"row sep\" for the table."
    colsep : String; "tikz-cd argument \"column sep\" for the table."

  ARGS:
    G : FgAb; FgAbDocstring
    A : RingOrCircle; RingOrCircleDocstring

  EXTENSIONS:
    defaultValues! #[("maxh", "10"), ("maxdeg", "20"), ("colsep", "tiny"), ("rowsep", "tiny")]
  ]
  where run p := do
    let maxDeg := p.flag! "maxdeg" |>.as! Nat
    let maxH := p.flag! "maxh" |>.as! Nat
    let rowsep := p.flag! "rowsep" |>.as! String
    let colsep := p.flag! "colsep" |>.as! String
    let G := p.positionalArg! "G" |>.as! FgAb
    let AArg := p.positionalArg! "A" |>.as! RingOrCircle
    let AName := latex AArg
    match AArg with
    | .Circle _ =>
      let ECss := Array.ofFn
        (λ h : Fin maxH => deloopGUpToDegree (R := Int) maxDeg (h + 1) G)
      let H := Array.ofFn (λ h : Fin maxH => BhGHomology' (R := Int) maxDeg (h + 1) G)

      let lowerECsMaps : Array (HashMap Path (ElementaryComplex Int)) :=
        ECss.map λ ECs => .ofList <| ECs.map λ EC => (EC.path, EC)
      let cosuspensions := lowerECsMaps.zipWith cosuspendℝℤ H

      abstractSuspensionTable H cosuspensions
        (names := λ h => BhGLaTexName h G)
        (cohomology := true)
        (displayℤAs := AName)
        (rowsep := rowsep)
        (colsep := colsep)
    | .Ring RArg =>
      let R := RArg.ring
      let ECss := Array.ofFn
        (λ h : Fin maxH => deloopGUpToDegree (R := R) maxDeg (h + 1) G)
      let H := Array.ofFn (λ h : Fin maxH => BhGCohomology' (R := R) maxDeg (h + 1) G)

      let lowerECsMaps : Array (HashMap Path (ElementaryComplex R)) :=
        ECss.map λ ECs => .ofList <| ECs.map λ EC => (EC.path, EC)
      let cosuspensions := lowerECsMaps.map cosuspend

      abstractSuspensionTable H cosuspensions
        (names := λ h => BhGLaTexName h G)
        (cohomology := true)
        (displayℤAs := AName)
        (rowsep := rowsep)
        (colsep := colsep)

    return 0

def latex := `[Cli|
  latex VIA run;
  "Generate a LaTeX table."

  SUBCOMMANDS:
    homology;
    cohomology;
    «suspension-chart»;
    «cosuspension-chart»;
    suspension;
    cosuspension
  ]
  where run p := do
    p.printHelp
    return 0

end LaTeX
export LaTeX (latex)
