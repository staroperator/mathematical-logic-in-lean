import Mathlib.Order.BoundedOrder

class PropNotation (α : Type u) where
  false : α
  imp : α → α → α

namespace PropNotation

variable [PropNotation α] (p q : α)
attribute [match_pattern] imp

instance : Bot α := ⟨false⟩
infixr:55 (priority := high) " ⇒ " => imp
abbrev neg (p : α) := p ⇒ ⊥
prefix:58 "~ " => neg
instance : Top α := ⟨~ ⊥⟩
def or (p q : α) := ~ p ⇒ q
infixl:56 " ⩒ " => or
def and (p q : α) := ~ (p ⇒ ~ q)
infixl:57 " ⩑ " => and
def iff (p q : α) := (p ⇒ q) ⩑ (q ⇒ p)
infix:55 (priority := high) " ⇔ " => iff

end PropNotation
