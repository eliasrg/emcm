import EMCM.Algebra.FgAb.Basic
import EMCM.Notation

namespace EMCM.Algebra.FgAb
open Notation

def directSum : FgAb → FgAb → FgAb
  | ⟨rank₁, torsion₁⟩, ⟨rank₂, torsion₂⟩ =>
    let torsion' := torsion₁.merge torsion₂ (·.1 ≤ ·.1)
      |>.map λ (p, fms) => (p, fms.mergeSort (·.1 ≤ ·.1))
    .normalize ⟨rank₁ + rank₂, torsion'⟩

instance : Oplus FgAb where oplus := directSum

instance : HPow FgAb Nat FgAb where
  hPow | ⟨rank, torsion⟩, n =>
         let torsion' := torsion.map <| .map id <| .map <| .map id (· * n)
         ⟨n * rank, torsion'⟩

/-- Tensor product of torsional parts -/
private partial def torsionTensor :
    List (Nat × List (Nat × Nat))
    → List (Nat × List (Nat × Nat))
    → List (Nat × List (Nat × Nat))
  | [], _
  | _, [] => []
  | G₁@((p₁, fms₁) :: T₁), G₂@((p₂, fms₂) :: T₂) =>
    if p₁ < p₂ then torsionTensor T₁ G₂
    else if p₂ < p₁ then torsionTensor G₁ T₂
    else (p₁, go fms₁ fms₂) :: torsionTensor T₁ T₂
where
  go | _, [] | [], _ => []
     | fms₁@((f₁, m₁) :: t₁), fms₂@((f₂, _) :: _) =>
       if f₂ < f₁ then go fms₂ fms₁
       else (f₁, m₁ * (fms₂.map (·.2) |>.sum)) :: go t₁ fms₂

def tensor : FgAb → FgAb → FgAb
  | ⟨rank₁, torsion₁⟩, ⟨rank₂, torsion₂⟩ =>
    ⟨rank₁ * rank₂, []⟩
    ⊕ ⟨0, torsion₂⟩^rank₁ ⊕ ⟨0, torsion₁⟩^rank₂
    ⊕ ⟨0, torsionTensor torsion₁ torsion₂⟩

instance : Otimes FgAb where otimes := tensor

def tor : FgAb → FgAb → FgAb
  | ⟨_, torsion₁⟩, ⟨_, torsion₂⟩ => ⟨0, torsionTensor torsion₁ torsion₂⟩

def ext : FgAb → FgAb → FgAb
  | ⟨_, torsion₁⟩, ⟨rank₂, torsion₂⟩ =>
        ⟨0, torsion₁⟩^rank₂ ⊕ ⟨0, torsionTensor torsion₁ torsion₂⟩

def hom : FgAb → FgAb → FgAb
  | G₁@⟨rank₁, _⟩, G₂ => G₂^rank₁ ⊕ tor G₁ G₂
