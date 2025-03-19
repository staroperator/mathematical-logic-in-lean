import Mathlib.Order.Notation

class PropNeg (α : Type u) where
  neg : α → α
prefix:58 "~ " => PropNeg.neg

class PropImp (α : Type u) where
  imp : α → α → α
infixr:55 (priority := high) " ⇒ " => PropImp.imp
attribute [match_pattern] PropImp.imp

class PropOr (α : Type u) where
  or : α → α → α
infixr:56 " ⩒ " => PropOr.or

class PropAnd (α : Type u) where
  and : α → α → α
infixr:57 " ⩑ " => PropAnd.and

class PropIff (α : Type u) where
  iff : α → α → α
infix:55 (priority := high) " ⇔ " => PropIff.iff

/-- Typeclass for propositional notations. -/
class PropNotation (α : Type u) extends Top α, Bot α, PropNeg α, PropImp α, PropOr α, PropAnd α, PropIff α

/--
  For classical logic, only `⊥` and `⇒` need to be defined; other notations are derived as follows:
  - Negation `~ p = p ⇒ ⊥`.
  - True `⊤ = ~ ⊥`.
  - Disjunction (or) `p ⩒ q = ~ p ⇒ q`.
  - Conjunction (and) `p ⩑ q = ~ (p ⇒ ~ q)`.
  - Iff `p ⇔ q = (p ⇒ q) ⩑ (q ⇒ p)`.
 -/
class ClassicalPropNotation (α : Type u) where
  false : α
  imp : α → α → α

namespace ClassicalPropNotation

variable {α : Type u} [ClassicalPropNotation α]

instance : Bot α := ⟨false⟩
instance : PropImp α := ⟨imp⟩

instance : PropNeg α where
  neg p := p ⇒ ⊥

instance : Top α where
  top := ~ ⊥

instance : PropOr α where
  or p q := ~ p ⇒ q

instance : PropAnd α where
  and p q := ~ (p ⇒ ~ q)

instance : PropIff α where
  iff p q := (p ⇒ q) ⩑ (q ⇒ p)

instance : PropNotation α where

variable {p q : α}
theorem true_def : (⊤ : α) = ~ ⊥ := rfl
theorem neg_def : ~ p = p ⇒ ⊥ := rfl
theorem or_def : p ⩒ q = ~ p ⇒ q := rfl
theorem and_def : p ⩑ q = ~ (p ⇒ ~ q) := rfl
theorem iff_def : p ⇔ q = (p ⇒ q) ⩑ (q ⇒ p) := rfl

end ClassicalPropNotation
