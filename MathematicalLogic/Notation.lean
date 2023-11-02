import Mathlib.Order.BoundedOrder
import Mathlib.Data.Vector

universe u

notation "[]ᵥ" => Vector.nil
infixr:67 "∷ᵥ" => Vector.cons

@[notation_class] class NotSymbol (α : Type u) where
  not : α → α

@[notation_class] class AndSymbol (α : Type u) where
  and : α → α → α

@[notation_class] class OrSymbol (α : Type u) where
  or : α → α → α

@[notation_class] class ImpSymbol (α : Type u) where
  imp : α → α → α

@[notation_class] class IffSymbol (α : Type u) where
  iff : α → α → α

@[notation_class] class ForallSymbol (α : Type u) where
  all : α → α

@[notation_class] class ExistsSymbol (α : Type u) where
  exist : α → α

prefix:58 "~ " => NotSymbol.not
infix:56 " ⋁ " => OrSymbol.or
infix:57 " ⋀ " => AndSymbol.and
infixr:55 " ⟶ " => ImpSymbol.imp
infix:55 " ⟷ " => IffSymbol.iff
prefix:59 "∀' " => ForallSymbol.all
prefix:59 "∃' " => ExistsSymbol.exist
attribute [match_pattern] NotSymbol.not OrSymbol.or AndSymbol.and ImpSymbol.imp IffSymbol.iff ForallSymbol.all ExistsSymbol.exist
