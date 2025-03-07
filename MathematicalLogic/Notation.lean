import Mathlib.Order.Notation

/--
  Typeclass for propositional notations. Only `⊥` and `⇒` need to be defined; other notations are derived as follows:
  - Negation `~ p = p ⇒ ⊥`.
  - True `⊤ = ~ ⊥`.
  - Disjunction (or) `p ⩒ q = ~ p ⇒ q`.
  - Conjunction (and) `p ⩑ q = ~ (p ⇒ ~ q)`.
  - Iff `p ⇔ q = (p ⇒ q) ⩑ (q ⇒ p)`.
 -/
class PropNotation (α : Type u) where
  false : α
  imp : α → α → α

namespace PropNotation

variable [PropNotation α] (p q : α)
attribute [match_pattern] imp

instance : Bot α := ⟨false⟩
infixr:55 (priority := high) " ⇒ " => imp
def neg (p : α) := p ⇒ ⊥
prefix:58 "~ " => neg
instance : Top α := ⟨~ ⊥⟩
def or (p q : α) := ~ p ⇒ q
infixr:56 " ⩒ " => or
def and (p q : α) := ~ (p ⇒ ~ q)
infixr:57 " ⩑ " => and
def iff (p q : α) := (p ⇒ q) ⩑ (q ⇒ p)
infix:55 (priority := high) " ⇔ " => iff

end PropNotation
