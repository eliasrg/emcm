import EMCM.Util.Script

namespace EMCM.Util

/-- Run-length encoding of a list of letters. -/
def rle (ls : List String) (latex : Bool := false) : String :=
    ls.splitBy (· == ·)
    |>.map (λ segment => segment[0]!
            ++ if segment.length == 1 then ""
            else if latex
                 then s!"^\{{segment.length}}"
                 else segment.length.superscript)
    |> .intercalate (if latex then " " else "")
