import EMCM.Algebra.ChainComplex.AtomicComplex
import EMCM.Algebra.ChainComplex.TensorProduct
import EMCM.Algebra.Homology.Generated
import EMCM.BhGHomology
import EMCM.ElementaryComplex.AtomicComplexes

import Std.Data.HashMap

namespace EMCM
open ElementaryComplex Algebra Structures ScalarMultiple
open Homology Ring PrincipalRing
open ChainComplex TensorProduct
open Std

variable [PrincipalRing R]

namespace ElementaryComplex

-- TODO: Get rid of order calculation, use lookup instead for simplicity and reliability
def suspendEC
  (ECs : HashMap Path (ElementaryComplex R))
  : HomologyGenerator R → HomologyGenerator R
  | .Scalar _ => 0
  | .Gen .Zero _ _ => unreachable!
  | .Gen (.Mul r g) d o =>
    let EC := ECs.get! g.path
    let (g', o') : ScalarMultiple ElementaryComplex.Generator R × Order
    := match EC, g with
    | .Λℤ .., .Word P a =>
      (r • Word (.σΛℤ P) (.σ a), o)
    | .ΛℤN .., .Word P@(.ΛℤN N ..) u =>
      let P' := if (N : R) == 0 then .σΛℤNₙ P else .σΛℤN P
      (r • Word P' (.σ u), o)
    | .AI .., .Word P x =>
      (r • Word (.σAI P) (.σ x), o)
    | .BI _ p .., .Word P (.γ' k x) =>
      match k.factor with
      | [(p', i + 1)] =>
        if p == 0 ∨ p == p' then
          let P' := if (p' : R) == 0 then .σγBIₚ p' i P else .σγBI p' i P
          (r • Word P' (.σ <| .γ' k x), gcd (0 : R) p')
        else (0, 1)
      | _ => (0, 1)
    | .BI .., .Word P x =>
      (r • Word (.σBI P) (.σ x), o)
    | .BII _ p .., .Word P (.γ' k x) =>
      match k.factor with
      | [(p', i + 1)] =>
        if p == 0 ∨ p == p' then
          let P' := if (p' : R) == 0 then .σγBIIₚ p' i P else .σγBII p' i P
          (r • Word P' (.σ <| .γ' k x), gcd (0 : R) p')
        else (0, 1)
      | _ => (0, 1)
    | .BII .., .Word P w => -- w is either x or y
      (r • Word (.σBII P) (.σ w), o)
    | .BII .., .Product .. => (0, 1)
    | .AII _ p _x _y _ η, .Word P (.γ' k y) =>
      assert! η != 0 ∧ gcd 0 η % p == 0
      match k.factor with
      | [(p', i + 1)] =>
        if p' == p then
          /- If p = 2 and i = 0, the answer is r(ε₂y - η/2 σx σy),
             which differs from rε₂y only when r is not divisible by 2.
             But since r = p^ℓ/gcd(η, p^ℓ), where the base ring is ℤ mod p^ℓ,
             this means that η = 0. Thus this case should never be reached. -/
          assert! η != 0
          (r • Word (.εAII p i P) (.ε (p^(i+1)) y), p)
        else (0, 1)
      | _ => (0, 1)
    | .AII .., .Word P x => (r • Word (.σAII P) (.σ x), o)
    | .AII .., .Product _ _x (.γ' _ _y) => (0, 1)
    | .AII _ p _x _y _ η, .Product P x _ =>
      if p == 2 ∧ gcd 2 r == 1
      then ((-η * r) • Word (.σAII P) (.γ 2 (.σ x)), 2)
      else (0, 1)
    | _, _ => (0, 1)
    (1 : R) • .Gen g' (d + 1) o'
  where
    Word := Generator.Word

def cosuspendEC (lowerECs : HashMap Path (ElementaryComplex R))
  : CohomologyGenerator R → CohomologyGenerator R
  | .Scalar _ => 0
  | .Gen .Zero _ _ => unreachable!
  | .Gen (.Mul r g) d o =>
    match g.path.tail with
    | none => 0
    | some P =>
      let EC := lowerECs.get! P
      let Word := Generator.Word P
      let (g', o') : ScalarMultiple ElementaryComplex.Generator R × Order
      := match EC, g with
      -- TODO change?
      | .Λℤ .., .Word _ (.σ a) => (r • Word a, o)
      | .ΛℤN .., .Word _ (.σ u) => (r • Word u, o)
      /- The above two should actually map (σa)* ↦ ∑ₙ n(a^n)*, and similarly for u,
         but we don't have a representation for a^n or u^n (and for a, the sum
         would be infinite). -/
      | .AI .., .Word _ (.σ x) => (r • Word x, o)
      | .AI .., .Word _ (.γ' ..) => (0, 1)
      | .BI .., .Word _ (.σ w) => (r • Word w, o)
      | .BI .., .Word _ _ => (0, 1)
      | .BII .., .Word _ (.σ w) => (r • Word w, o)
      | .BII .., .Word _ _ => (0, 1)
      | .AII .., .Word _ (.ε' k y) => (r • Word (.γ k y), o.toNat / gcd r o)
      | .AII .., .Word _ (.σ w) => (r • Word w, o)
      | .AII _ p x y _ η, .Product _ (.σ x') (.σ y') =>
        assert! x == x' ∧ y == y'
        if p == 2 ∧ gcd 2 r == 1 then
          let ηhalf : R := (toInt η / 2 : Int)
          ((r * -ηhalf) • Word (.γ 2 y), 2)
        else (0, 1)
      | _, _ => (0, 1)
      (1 : R) • .Gen g' (d + 1) o'

end ElementaryComplex

def suspend (ECs : HashMap Path (ElementaryComplex R))
  : BhGHomologyGenerator R → BhGHomologyGenerator R
  | .Gen (.Mul r (.Basic g)) d o =>
    match suspendEC ECs (.Gen (r • g) d o) with
    | .Gen (.Mul r' g') d' o' =>
      .Gen (r' • TPGenerator.Basic g') d' o'
    | _ => 0
  | _ => 0

def cosuspend (lowerECs : HashMap Path (ElementaryComplex R))
  : BhGCohomologyGenerator R → BhGCohomologyGenerator R
  | .Gen (.Mul r (.Basic g)) d o =>
    match cosuspendEC lowerECs (.Gen (r • g) d o) with
    | .Gen (.Mul r' g') d' o' =>
      .Gen (r' • TPGenerator.Basic g') d' o'
    | _ => 0
  | _ => 0

-- TODO I don't think that this "returns a closure".
def cosuspendℝℤ
  (lowerECs : HashMap Path (ElementaryComplex Int))
  (lowerHomology : BhGHomologyComplex Int)
  : BhGℝℤCohomologyGenerator → BhGℝℤCohomologyGenerator :=
  let suspensions : Array (
    HashMap ElementaryComplex.Generator
            (BhGHomologyGenerator Int × BhGHomologyGenerator Int)) :=
    #[{}] ++
    lowerHomology.map λ gens =>
      .ofArray <| gens.filterMap λ hg =>
        match suspend lowerECs hg with
        | shg@(.Gen (.Mul _ (.Basic sg)) _ _) => some (sg, shg, hg)
        | _ => none

  λ | .Gen (.Mul r (.Basic sg)) d _ =>
      Option.getD (dflt := 0) <| do
        if let (.Gen (.Mul sc (.Basic sg')) _ so,
                hg@(.Gen (.Mul c (.Basic _g)) _ o))
                ← (← suspensions[d]?).get? sg
        then
          assert! c == 1 ∧ sg == sg'
          return match so.isFinite, o.isFinite with
          | true, true =>
            /- We have g* = 1/o δ_g, and sc sg* = 1/so δ_sg.
               Ω(sg*) = sg* ∘ σ = sg*(σg) δ_g
                      = o/(so sc) δ_sg(σg) g*
                      = sc o/(so sc) g*
                      = sc o/(so sc) g*
                      = o/so g*. -/
            (r * o / so) • hg
          | true, false => 0
          | false, true => unreachable!
          | false, false =>
            assert! sc == 1
            r • hg
        else
          return 0
    | _ => 0
