import EMCM
import Cli

open EMCM
open Algebra ZMod FgAb Structures
open Cli

def PosNat := Nat
instance : ParseableType PosNat where
  name := "Nat > 0"
  parse? s := do
    let n ← s.toNat?
    guard (n > 0)
    return n

instance : ParseableType FgAb where
  name := "FgAb"
  parse? s := do
    let ns ← s.splitOn "+" |>.map String.toList |>.mapM
      λ | ['Z'] => return 0
        | 'Z' :: s => String.ofList s |>.toNat?
        | _ => failure
    return ns.foldl (·.directSum <| ℤN ·) 0

def FgAbDocstring : String :=
  "A finitely generated abelian group, given by an expression \
of the form <G₁>+<G₂>+⋯ where each Gᵢ is of the form \
Z or Z<n>. For example, Z+Z+Z2+Z3+Z3 denotes ℤ² ⊕ ℤ₂ ⊕ (ℤ₃)². The
expression is normalised using the Chinese Remainder Theorem, \
so that e.g. Z12 becomes ℤ₄ ⊕ ℤ₃."

structure LocalRing where
  Local::
  p : Nat

instance : ToString LocalRing where
  toString | .Local p => s!"ℤ₍{p.subscript}₎"

instance : ToString LocalRing where
  toString | .Local p => s!"ℤ₍{p.subscript}₎"

instance : LaTeX LocalRing where
  latex | .Local p => s!"\\mathbb\{Z}_\{({p})}"

instance : ParseableType LocalRing where
  name := "LocalRing"
  parse? s := do
    let 'L' :: nS := s.toList | failure
    let n ← String.ofList nS |>.toNat?
    guard n.isPrime
    return (.Local n)

def LocalRingDocstring := "The ring ℤ₍ₚ₎ (ℤ localised at a prime p), written L<p>"

inductive CoeffRing where
  | Z
  | Zpk (pk : Nat)
  | Local (L : LocalRing)
  deriving Inhabited

instance : ToString CoeffRing where
  toString | .Z => "ℤ"
           | .Zpk pk => s!"ℤ{pk.subscript}"
           | .Local L => toString L

instance : LaTeX CoeffRing where
  latex | .Z => r"\mathbb{Z}"
        | .Zpk pk => s!"\\mathbb\{Z}_\{{pk}}"
        | .Local L => latex L

instance : ParseableType CoeffRing where
  name := "Ring"
  parse? s :=
    .Local <$> ParseableType.parse? s
    <|> match s.toList with
    | ['Z'] => return .Z
    | 'Z' :: nS => do
      let n ← String.ofList nS |>.toNat?
      guard (n.factor.length == 1)
      return (.Zpk n)
    | _ => failure

abbrev CoeffRing.ring : CoeffRing → Type
  | .Z => Int
  | .Zpk pk => ZMod pk
  | .Local (.Local p) => pLocal p

instance (R : CoeffRing) : PrincipalRing R.ring := by
  cases R <;> simp [CoeffRing.ring] <;> infer_instance
instance (R : CoeffRing) : ToString R.ring := by
  cases R <;> simp [CoeffRing.ring] <;> infer_instance
instance (R : CoeffRing) : LaTeX R.ring := by
  cases R <;> simp [CoeffRing.ring] <;> infer_instance

def CoeffRingDocstring : String :=
  s!"One of the following:
· The ring ℤ, written Z
· The ring ℤₘ, where m is a prime power, written Z<m>
· {LocalRingDocstring}"

inductive CircleGroup where
  | RZ
  | U1
  deriving Inhabited

instance : ToString CircleGroup where
  toString | .RZ => "ℝ/ℤ"
           | .U1 => "U(1)"

instance : LaTeX CircleGroup where
  latex | .RZ => r"\mathbb{R}/\mathbb{Z}"
        | .U1 => "U(1)"

instance : ParseableType CircleGroup where
  name := "CircleGroup"
  parse? | "RZ" => return .RZ
         | "U1" => return .U1
         | _ => failure

def CircleGroupDocstring : String :=
"The group ℝ/ℤ ≅ U(1), written RZ or U1"

inductive RingOrCircle where
  | Ring (R : CoeffRing)
  | Circle (C : CircleGroup)
  deriving Inhabited

instance : ToString RingOrCircle where
  toString | .Ring R => toString R
           | .Circle C => toString C

instance : LaTeX RingOrCircle where
  latex | .Ring R => latex R
        | .Circle C => latex C

instance : ParseableType RingOrCircle where
  name := "Ab"
  parse? s := .Ring <$> ParseableType.parse? s
          <|> .Circle <$> ParseableType.parse? s

def RingOrCircleDocstring : String :=
  s!"{CoeffRingDocstring}
· {CircleGroupDocstring}"

inductive FgAbOrLocal where
  | FgAb (A : FgAb)
  | Local (L : LocalRing)
  deriving Inhabited

instance : ToString FgAbOrLocal where
  toString | .FgAb A => toString A
           | .Local L => toString L

instance : LaTeX FgAbOrLocal where
  latex | .FgAb R => latex R
        | .Local L => latex L

instance : ParseableType FgAbOrLocal where
  name := "Ab"
  parse? s := .FgAb <$> ParseableType.parse? s
          <|> .Local <$> ParseableType.parse? s

def FgAbOrLocalDocstring : String :=
  s!"One of:
· A finitely generated abelian group, written like G.
· {LocalRingDocstring}"

inductive FgAbOrLocalOrCircle where
  | FgAb (A : FgAb)
  | Local (L : LocalRing)
  | Circle (C : CircleGroup)
  deriving Inhabited

instance : ToString FgAbOrLocalOrCircle where
  toString | .FgAb A => toString A
           | .Local L => toString L
           | .Circle C => toString C

instance : LaTeX FgAbOrLocalOrCircle where
  latex | .FgAb R => latex R
        | .Local L => latex L
        | .Circle C => latex C

instance : ParseableType FgAbOrLocalOrCircle where
  name := "Ab"
  parse? s := .FgAb <$> ParseableType.parse? s
          <|> .Local <$> ParseableType.parse? s
          <|> .Circle <$> ParseableType.parse? s

def FgAbOrLocalOrCircleDocstring : String :=
  s!"{FgAbOrLocalDocstring}
· {CircleGroupDocstring}"
