/-- Convert a natural number to a subscript ASCII string. -/
def Nat.subscript (n : Nat) : String :=
  .ofList <| (10).toDigits n |>.map λ
    | '0' => '₀'
    | '1' => '₁'
    | '2' => '₂'
    | '3' => '₃'
    | '4' => '₄'
    | '5' => '₅'
    | '6' => '₆'
    | '7' => '₇'
    | '8' => '₈'
    | '9' => '₉'
    | _ => unreachable!

/-- Convert a natural number to a superscript ASCII string. -/
def Nat.superscript (n : Nat) : String :=
  .ofList <| (10).toDigits n |>.map λ
    | '0' => '⁰'
    | '1' => '¹'
    | '2' => '²'
    | '3' => '³'
    | '4' => '⁴'
    | '5' => '⁵'
    | '6' => '⁶'
    | '7' => '⁷'
    | '8' => '⁸'
    | '9' => '⁹'
    | _ => unreachable!
