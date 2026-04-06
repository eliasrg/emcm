import EMCM.Algebra.FgAb.Basic

namespace EMCM.Algebra.FgAb

set_option linter.unusedVariables false in
abbrev DisplayingℤAs (s : String) := FgAb

instance (s : String) : ToString (DisplayingℤAs s) where
  toString := toStringWithℤAs s

instance (s : String) : LaTeX (DisplayingℤAs s) where
  latex := toLaTeXWithℤAs s

def displayℤAs (s : String) : FgAb → DisplayingℤAs s := id
