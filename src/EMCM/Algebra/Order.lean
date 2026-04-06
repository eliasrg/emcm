import EMCM.Util.LaTeX

namespace EMCM.Algebra

def Order := Nat

def Order.toNat : Order → Nat := id
def Order.isFinite (o : Order) : Bool := o.toNat > 0

instance : ToString Order where
  toString : Nat → String
    | 0 => "∞"
    | n => toString n

instance : LaTeX Order where
  latex : Nat → String
    | 0 => "\\infty"
    | n => toString n

instance (n : Nat) : OfNat Order n where ofNat := n
instance : Coe Order Nat where coe := id
instance : Repr Order where reprPrec n _ := toString n

instance : Inhabited Order := inferInstanceAs (Inhabited Nat)
instance : Hashable Order := inferInstanceAs (Hashable Nat)
instance : DecidableEq Order := inferInstanceAs (DecidableEq Nat)
instance : BEq Order := inferInstanceAs (BEq Nat)
instance : Add Order := inferInstanceAs (Add Nat)
instance : Sub Order := inferInstanceAs (Sub Nat)
instance : Mul Order := inferInstanceAs (Mul Nat)
instance : Div Order := inferInstanceAs (Div Nat)
instance : HMul Nat Order Nat := inferInstanceAs (HMul Nat Nat Nat)
instance : HDiv Nat Order Nat := inferInstanceAs (HDiv Nat Nat Nat)
