import Mathlib.Order.BoundedOrder
import Mathlib.Data.Vector

universe u v

notation "[]ᵥ" => Vector.nil
infixr:67 "∷ᵥ" => Vector.cons

class FormulaSymbol (α : Type u) where
  false : α
  imp : α → α → α

namespace FormulaSymbol

variable [FormulaSymbol α] (p q : α)

instance : Bot α := ⟨false⟩

infixr:55 " ⟶ " => imp
attribute [match_pattern] imp

def neg := p ⟶ ⊥
prefix:58 "~ " => neg

instance : Top α := ⟨~ ⊥⟩

def or := ~ p ⟶ q
infix:56 " ⋁ " => or

def and := ~ (p ⟶ ~ q)
infix:57 " ⋀ " => and

def iff := (p ⟶ q) ⋀ (q ⟶ p)
infix:55 " ⟷ " => iff

end FormulaSymbol

@[notation_class] class EquivSymbol (α : Type u) (β : outParam (Type v)) where
  equiv : α → α → β

infix:70 " ≈ " => EquivSymbol.equiv
