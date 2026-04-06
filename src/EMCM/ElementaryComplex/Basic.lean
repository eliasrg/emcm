import EMCM.Util
import EMCM.Algebra.FgAb.Basic
import EMCM.Algebra.Structures
import Std.Data.Iterators

namespace EMCM
open Algebra FgAb Structures PrincipalRing

namespace ElementaryComplex

/-- A label for an algebra generator in an elementary complex. -/
inductive Word where
  /-- A generator of an infinite cyclic group. -/
  | a (index : Option Nat)
  /-- A generator of a finite cyclic group of order N. -/
  | u (N : Nat) (index : Option Nat)
  /-- The degree-2 generator in the delooping of the group
algebra of a finite cyclic group of order N. -/
  | ψ (N : Nat) (w : Word)
  /-- The divided power γₖ (degree d → kd).
Use the smart constructor γ instead of this constructor. -/
  | γ' (k : Nat) (w : Word)
  /-- The "suspension" σ (degree d ↦ d + 1). -/
  | σ (w : Word)
  /-- The "transpotence" φₚ (degree d ↦ pd + 2). -/
  | φ (p : Nat) (w : Word)
  /-- The letter εₖ, a basis-changed version of σγₖ
in the delooping of type-AII complexes (degree d ↦ pd + 1).
Use the smart constructor ε instead of this constructor. -/
  | ε' (k : Nat) (w : Word)
  deriving Inhabited, BEq, Hashable

/-- The divided power γₖ (degree d → kd), with γ₁ = id. -/
def Word.γ : (k : Nat) → (w : Word) → Word
  | 0, _ => panic! "γ₀ called"
  | 1, w => w
  | k, w => .γ' k w

/-- The letter εₖ, a basis-changed version of σγₖ
in the delooping of type-AII complexes (degree d ↦ pd + 1).
Subject to ε₁ = σ. -/
def Word.ε : (k : Nat) → (w : Word) → Word
  | 1, w => .σ w
  | k, w => .ε' k w

instance : ToString Word where
  toString := Util.rle ∘ letters
where
  /-- Turn a word into a list of letters. -/
  letters : Word → List String
    | .a none => ["a"]
    | .a (some i) => [s!"a₍{i.subscript}₎"]
    | .u N none => [s!"u{N.subscript}"]
    | .u N (some i) => [s!"u{N.subscript}₍{i.subscript}₎"]
    | .ψ N w => s!"ψ{N.subscript}" :: letters w
    | .γ' i w => s!"γ{i.subscript}" :: letters w
    | .σ w => "σ" :: letters w
    | .φ p w => s!"φ{p.subscript}" :: letters w
    | .ε' k w => s!"ε{k.subscript}" :: letters w

instance : LaTeX Word where
  latex := Util.rle (latex := true) ∘ letters
where
  /-- Turn a word into a list of letters. -/
  letters : Word → List String
    | .a none => ["a"]
    | .a (some i) => [s!"a_\{({i})}"]
    | .u N none => [s!"u_\{{N}}"]
    | .u N (some i) => [s!"u_\{{N}}_\{({i})}"]
    | .ψ N w => s!"\\psi_\{{N}}" :: letters w
    | .γ' i w => s!"\\gamma_\{{i}}" :: letters w
    | .σ w => "\\sigma" :: letters w
    | .φ p w => s!"\\varphi_\{{p}}" :: letters w
    | .ε' k w => s!"\\varepsilon_\{{k}}" :: letters w

/-- A description for the process used to construct an elementary complex. -/
inductive Path where
  /-- The group algebra of an infinite cyclic group. -/
  | Λℤ (ix : Option Nat)
  /-- The group algebra of a finite cyclic group of order N. -/
  | ΛℤN (N : Nat) (ix : Option Nat)

  /-- The complex AI(σa, 1) in the delooping of Λ[ℤ]. -/
  | σΛℤ (P : Path)
  /-- The complex AII(σu, ψu, 1, N) in the delooping of Λ[ℤ_N]. -/
  | σΛℤN (P : Path)
  /-- The complex AI(σu, 1) in the delooping of Λ[ℤ_N] mod N. -/
  | σΛℤNₙ (P : Path)
  /-- The complex BI(ψu, 2) in the delooping of Λ[ℤ_N] mod N. -/
  | ψΛℤNₙ (P : Path)

  /-- The complex BI(σx, n+1) in the delooping of AI(x, n). -/
  | σAI (P : Path)

  /-- The complex AI(σx, n+1) in the delooping of BI(x, n). -/
  | σBI (P : Path)
  /-- The complex AII(σγ_{p^(i+1)} x, φ_p γ_{p^i} x, p^{i+1} n + 1, -pζᵢ)
in the delooping of BI(x, n) over ℤ₍ₚ₎. -/
  | σγBI (p i : Nat) (P : Path)
  /-- The complex AI(σγ_{p^(i+1)} x, p^{i+1} n + 1)
in the delooping of BI(x, n) mod p. -/
  | σγBIₚ (p i : Nat) (P : Path)
  /-- The complex BI(φ_p γ_{p^i} x, p^{i+1} n + 2)
in the delooping of BI(x, n) mod p. -/
  | φγBIₚ (p i : Nat) (P : Path)

  /-- The complex BII(σx, σy, n+1, -η) in the delooping of AII(x, y, n, η) over ℤ₍ₚ₎. -/
  | σAII (P : Path)
  /-- The complex AII(ε_{p^{i+1}} y, φ_p γ_{p^i} y, p^{i+1} (n + 1) + 1, -pζᵢ)
in the delooping of AII(x, y, n, η) over ℤ₍ₚ₎. -/
  | εAII (p i : Nat) (P : Path)
  /-- The complex AI(σγ_{p^(i+1)} y, p^{i+1} (n + 1) + 1)
in the delooping of AII(x, y, n, η) mod p. -/
  | σγAIIₚ (p i : Nat) (P : Path)
  /-- The complex BI(φ_p γ_{p^i} y, p^{i+1} (n + 1) + 2)
in the delooping of AII(x, y, n, η) mod p. -/
  | φγAIIₚ (p i : Nat) (P : Path)

  /-- The complex AII(σx, σy, n+1, -η) in the delooping of BII(x, y, n, η) over ℤ₍ₚ₎. -/
  | σBII (P : Path)
  /-- The complex AII(σγ_{p^(i+1)} x, φ_p γ_{p^i} x, p^{i+1} n + 1, -pζᵢ)
in the delooping of BII(x, y, n, η) over ℤ₍ₚ₎. -/
  | σγBII (p i : Nat) (P : Path)
  /-- The complex AI(σγ_{p^(i+1)} x, p^{i+1} n + 1)
in the delooping of BII(x, y, n, η) mod p. -/
  | σγBIIₚ (p i : Nat) (P : Path)
  /-- The complex BI(φ_p γ_{p^i} x, p^{i+1} n + 2)
in the delooping of BII(x, y, n, η) mod p. -/
  | φγBIIₚ (p i : Nat) (P : Path)
  deriving Inhabited, BEq, Hashable

def Path.tail : Path → Option Path
  | .Λℤ ..
  | .ΛℤN ..
  => none
  | .σΛℤ P | .σΛℤN P | .σΛℤNₙ P | .ψΛℤNₙ P
  | .σAI P
  | .σBI P | .σγBI _ _ P | .σγBIₚ _ _ P | .φγBIₚ _ _ P
  | .σAII P | .εAII _ _ P | .σγAIIₚ _ _ P | .φγAIIₚ _ _ P
  | .σBII P | .σγBII _ _ P | .σγBIIₚ _ _ P | .φγBIIₚ _ _ P
  => P

instance : ToString Path where
  toString := "→".intercalate ∘ .reverse ∘ letters
  where letters
  | .Λℤ none => ["Λℤ"]
  | .Λℤ (some i) => [s!"Λℤ₍{i.subscript}₎"]
  | .ΛℤN N none => [s!"Λℤ{N.subscript}"]
  | .ΛℤN N (some i) => [s!"Λℤ{N.subscript}₍{i.subscript}₎"]
  | .σΛℤ P => "σΛℤ" :: letters P
  | .σΛℤN P => "σΛℤN" :: letters P
  | .σΛℤNₙ P => "σΛℤNₙ" :: letters P
  | .ψΛℤNₙ P => "ψΛℤNₙ" :: letters P
  | .σAI P => "σAI" :: letters P
  | .σBI P => "σBIℤ" :: letters P
  | .σγBI p i P => s!"σγ{p^(i+1) |>.subscript}BI" :: letters P
  | .σγBIₚ p i P => s!"σγ{p^(i+1) |>.subscript}BI{p.subscript}" :: letters P
  | .φγBIₚ p i P => s!"φγ{p^i |>.subscript}BI{p.subscript}" :: letters P
  | .σAII P => "σAII" :: letters P
  | .εAII p i P => s!"ε{p^(i+1) |>.subscript}AII" :: letters P
  | .σγAIIₚ p i P => s!"σγ{p^(i+1) |>.subscript}AII{p.subscript}" :: letters P
  | .φγAIIₚ p i P => s!"φγ{p^i |>.subscript}AII{p.subscript}" :: letters P
  | .σBII P => "σBII" :: letters P
  | .σγBII p i P => s!"σγ{p^(i+1) |>.subscript}BII" :: letters P
  | .σγBIIₚ p i P => s!"σγ{p^(i+1) |>.subscript}BII{p.subscript}" :: letters P
  | .φγBIIₚ p i P => s!"φγ{p^i |>.subscript}BII{p.subscript}" :: letters P

end ElementaryComplex

open ElementaryComplex in
/-- An elementary complex over the base ring Λ = ℤ₍ₚ₎.
We allow p = 0 in the first four cases, to mean Λ = ℤ. -/
inductive ElementaryComplex R [Ring R] where
  /-- The group algebra ℤ₍ₚ₎[ℤ] = ℤ₍ₚ₎[a,a⁻¹] / (a a⁻¹ - 1) -/
  | Λℤ (P : Path) (p : Nat) (a : Word)
  /-- The group algebra ℤ₍ₚ₎[ℤ/Nℤ] = ℤ₍ₚ₎[u] / (uᴺ - 1) -/
  | ΛℤN (P : Path) (p : Nat) (N : Nat) (u : Word)
  /-- The exterior algebra E(x, n) (n odd). -/
  | AI (P : Path) (p : Nat) (x : Word) (n : Nat)
  /-- The divided polynomial algebra Γ(x, n) (n even). -/
  | BI (P : Path) (p : Nat) (x : Word) (n : Nat)
  /-- The algebra E(x, n) ⊗ Γ(y, n + 1) with ∂y = ηx
(n odd, η divisible by p). -/
  | AII (P : Path) (p : Nat) (x y : Word) (n : Nat) (η : R)
  /-- The algebra Γ(x, n) ⊗ E(y, n + 1) with ∂y = ηx
(n even, η divisible by p). -/
  | BII (P : Path) (p : Nat) (x y : Word) (n : Nat) (η : R)
  deriving Inhabited, BEq

namespace ElementaryComplex
variable [Ring R]

instance [ToString R] : ToString (ElementaryComplex R) where
  -- toString does not display the path
  toString
  | .Λℤ _ p a => s!"{baseRing R p}[ℤ⟨{a}⟩]"
  | .ΛℤN _ p N u => s!"{baseRing R p}[ℤ{N.subscript}⟨{u}⟩]"
  | .AI _ p x n => s!"AI{p.subscript}({x}, {n})"
  | .BI _ p x n => s!"BI{p.subscript}({x}, {n})"
  | .AII _ p x y n η => s!"AII{p.subscript}({x}, {y}, {n}, {η})"
  | .BII _ p x y n η => s!"BII{p.subscript}({x}, {y}, {n}, {η})"
  where baseRing R [Ring R] (p : Nat) : String :=
          match Ring.characteristic R with
          | 0 => if p == 0 then "ℤ" else s!"ℤ₍{p.subscript}₎"
          | c => s!"ℤ{(c.primeComponent p).subscript}"

def path : ElementaryComplex R → Path
  | .Λℤ P .. | .ΛℤN P ..
  | .AI P .. | .BI P ..
  | .AII P .. | .BII P .. => P

def prime : ElementaryComplex R → Nat
  | .Λℤ _ p .. | .ΛℤN _ p ..
  | .AI _ p .. | .BI _ p ..
  | .AII _ p .. | .BII _ p .. => p

/-- The degree of the lowest-degree generator of a complex. -/
def degree : ElementaryComplex R → Nat
  | .Λℤ .. | .ΛℤN .. => 0
  | .AI _ _ _ n | .BI _ _ _ n
  | .AII _ _ _ _ n _ | .BII _ _ _ _ n _ => n

def η : ElementaryComplex R → R
  | .AII _ _ _ _ _ η
  | .BII _ _ _ _ _ η => η
  | _ => 0

def tryDecompose (c : ElementaryComplex R) : List (ElementaryComplex R) :=
  if c.η == 0 then
    match c with
    | .AII (.σΛℤN P) p x y n _ =>
      [.AI (.σΛℤNₙ P) p x n, .BI (.ψΛℤNₙ P) p y (n + 1)]
    | .AII (.σγBI p i P) _ x y n _ =>
      [.AI (.σγBIₚ p i P) p x n, .BI (.φγBIₚ p i P) p y (n + 1)]
    | .AII (.εAII p i P) _ x y n _ =>
      [.AI (.σγAIIₚ p i P) p x n, .BI (.φγAIIₚ p i P) p y (n + 1)]
    | .AII (.σBII _) .. =>
      panic! "Decomposition of AII (σBII ⋯) ⋯ should have happened earlier"
    | .AII (.σγBII p i P) _ x y n _ =>
      [.AI (.σγBIIₚ p i P) p x n, .BI (.φγBIIₚ p i P) p y (n + 1)]
    | .BII (.σAII _) .. =>
      panic! "Decomposition of BII (σAII ⋯) ⋯ should have happened earlier"
    | _ => [c]
  else [c]

/-- The integer ζₚ,ᵢ = (p^(i+1))! / (p (p^i)!^p) (coprime to p). -/
def ζ (p i : Nat) : Nat :=
  (p^(i+1)).factorial / (p * (p^i).factorial^p)

end ElementaryComplex

namespace ElementaryComplex
variable [PrincipalRing R]

/-- All elementary complexes with degree ≤ `maxDeg`
in the delooping of c. -/
def deloopUpToDegree
  (maxDeg : Nat)
  (c : ElementaryComplex R)
  (discardUnits : Bool := false)
  : List (ElementaryComplex R) :=
  .filter (·.degree ≤ maxDeg)
  ∘ .flatMap ElementaryComplex.tryDecompose
  <| match c with
  | .Λℤ P p a => [.AI (.σΛℤ P) p (.σ a) 1]
  | .ΛℤN P p N u => [.AII (.σΛℤN P) p (.σ u) (.ψ N u) 1 N]
  | .AI P p x n => [.BI (.σAI P) p (.σ x) (n + 1)]
  | .BI P p x n =>
    .AI (.σBI P) p (.σ x) (n + 1) :: (
      -- Over ℤ, "deloop" to ℤ₍ₚ₎ for all p
      let primes : List Nat :=
        if p == 0 then
          Nat.primesUpTo ((maxDeg - 1) / n)
          |>.filter λ p => gcd (R := R) p 0 != 1
        else [p]
      primes.flatMap λ p =>
      (0...*).iter
      |>.map (λ i => .AII (.σγBI p i P) p
                          (.σ <| .γ (p^(i+1)) x)
                          (.φ p <| .γ (p^i) x)
                          (p^(i+1) * n + 1) (-p * ζ' p i))
      |>.takeWhile (·.degree ≤ maxDeg)
      |>.toList)
  | .AII P p x y n η => assert! p > 0
    .BII (.σAII P) p (.σ x) (.σ y) (n + 1) (-η) :: (
      (0...*).iter
      |>.map (λ i => .AII (.εAII p i P) p
                          (.ε (p^(i+1)) y)
                          (.φ p <| .γ (p^i) y)
                          (p^(i+1) * (n + 1) + 1) (-p * ζ' p i))
      |>.takeWhile (·.degree ≤ maxDeg)
      |>.toList)
  | .BII P p x y n η => assert! p > 0
    .AII (.σBII P) p (.σ x) (.σ y) (n + 1) (-η) :: (
      (0...*).iter
      |>.map (λ i => .AII (.σγBII p i P) p
                          (.σ <| .γ (p^(i+1)) x)
                          (.φ p <| .γ (p^i) x)
                          (p^(i+1) * n + 1) (-p * ζ' p i))
      |>.takeWhile (·.degree ≤ maxDeg)
      |>.toList)
  where ζ' p i := if discardUnits then 1 else ζ p i

/-- All elementary complexes with degree ≤ maxDeg
resulting from h deloopings of a set of initial complexes. -/
def deloopRecUpToDegree
  (maxDeg h : Nat)
  (cs₀ : List (ElementaryComplex R))
  (discardUnits : Bool := false)
  : List (ElementaryComplex R) :=
  h.fold (λ _ _ cs =>
    cs.flatMap (·.deloopUpToDegree maxDeg discardUnits)) cs₀

def groupAlgebra [PrincipalRing R]
  : FgAb → List (ElementaryComplex R)
  | ⟨rank, torsion⟩ =>
    let Λℤs :=
      (1...=rank).toList.map λ i =>
      let ix := if rank == 1 then none else some i
      .Λℤ (.Λℤ ix) 0 (.a ix)
    let ΛℤNs :=
      torsion.filter (λ (p, _) => gcd (R := R) p 0 != 1)
      |>.flatMap λ (p, fms) =>
      fms.flatMap λ (f, m) =>
      (1...=m).toList.map λ i =>
      let ix := if m == 1 then none else some i
      .ΛℤN (.ΛℤN (p^f) ix) p (p^f) (.u (p^f) ix)
    Λℤs ++ ΛℤNs

def deloopGUpToDegree [PrincipalRing R]
  (maxDeg h : Nat)
  (G : FgAb)
  (discardUnits : Bool := false)
  : List (ElementaryComplex R) :=
  deloopRecUpToDegree maxDeg h (groupAlgebra G) discardUnits

end ElementaryComplex
