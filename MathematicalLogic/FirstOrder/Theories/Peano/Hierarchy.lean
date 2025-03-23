import MathematicalLogic.FirstOrder.Theories.Peano.Theory

/-!

# Arithmetic Hierarchy

This file defines Σ₁ formulas in arithmetic hierarchy and ω-consistency. Current we are not
interested in defining the whole arithmetic hierarchy.

-/

namespace FirstOrder.Language.peano

/--
  The set of Σ₁ formulas is closed under conjunction, disjunction, existential quantifier and
  bounded universal quantifier. This is a strict syntactic definition, mainly used to prove
  Hilbert-Bernays provability conditions.
  -/
@[aesop safe] inductive Sigma₁ : peano.Formula n → Prop where
| eq : Sigma₁ (t₁ ≐ t₂)
| neq : Sigma₁ (~ t₁ ≐ t₂)
| false : Sigma₁ ⊥
| true : Sigma₁ ⊤
| and : Sigma₁ p → Sigma₁ q → Sigma₁ (p ⩑ q)
| or : Sigma₁ p → Sigma₁ q → Sigma₁ (p ⩒ q)
| ex : Sigma₁ p → Sigma₁ (∃' p)
| bdall : Sigma₁ p → Sigma₁ (∀[≺ t] p)

@[aesop safe] theorem Sigma₁.le : Sigma₁ (t₁ ⪯ t₂) := by simp [le_def]; aesop

@[aesop safe] theorem Sigma₁.lt : Sigma₁ (t₁ ≺ t₂) := by simp [lt_def]; aesop

@[aesop safe] theorem Sigma₁.andN {v : Vec (peano.Formula n) m} :
  (∀ i, Sigma₁ (v i)) → Sigma₁ (⋀ i, v i) := by
  intro h
  induction m <;> simp [Formula.andN] <;> aesop

@[aesop safe] theorem Sigma₁.orN {v : Vec (peano.Formula n) m} :
  (∀ i, Sigma₁ (v i)) → Sigma₁ (⋁ i, v i) := by
  intro h
  induction m <;> simp [Formula.orN] <;> aesop

@[aesop safe] theorem Sigma.exN {p : peano.Formula (n + m)} : Sigma₁ p → Sigma₁ (∃^[m] p) := by
  induction m <;> simp [Formula.exN]; aesop

@[aesop safe] theorem Sigma.bdex : Sigma₁ p → Sigma₁ (∃[≺ t] p) := by simp [Order.bdex]; aesop

@[aesop safe] theorem Sigma₁.subst {σ : peano.Subst n m} : Sigma₁ p → Sigma₁ (p[σ]ₚ) := by
  intro h
  induction h generalizing m <;> simp <;> aesop

open Proof Theory

/-- A theory is ω-consistent if it does not prove both `∃ x. p(x)` and `p(0), p(1), ⋯`. -/
def OmegaConsistent (T : peano.Theory) :=
  ∀ p, ¬ (T ⊢ ∃' p ∧ ∀ (n : ℕ), T ⊢ ~ p[↦ₛ n]ₚ)

theorem OmegaConsistent.consistent : OmegaConsistent T → Consistent T := by
  intro h p
  apply h ⊥
  constructor
  · papply Proof.false_elim; exact p
  · intro; exact Proof.false_elim

end FirstOrder.Language.peano
