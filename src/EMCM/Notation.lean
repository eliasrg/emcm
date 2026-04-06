namespace EMCM.Notation

class Oplus (α : Type) where
  oplus : α → α → α
infixr:30 " ⊕ " => Oplus.oplus

class Otimes (α : Type) where
  otimes : α → α → α
infixr:35 " ⊗ " => Otimes.otimes
