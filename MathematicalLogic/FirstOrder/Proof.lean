import Mathlib.Data.Set.Finite
import MathematicalLogic.FirstOrder.Syntax

@[reducible] def Formulas (𝓛) := Set (Formula 𝓛)

def Formulas.add (Γ : Formulas 𝓛) (p) := insert p Γ
infixl:51 ",' " => Formulas.add

def Formulas.lift : Formulas 𝓛 → Formulas 𝓛 := λ Γ => {↑ₚp | p ∈ Γ}
prefix:max "↑ₚₛ" => Formulas.lift

inductive Axioms (𝓛) : Formulas 𝓛 where
| a1 : Axioms 𝓛 (p ⟶ (q ⟶ p))
| a2 : Axioms 𝓛 ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
| a3 : Axioms 𝓛 ((~ p ⟶ ~ q) ⟶ q ⟶ p)
| a4 : Axioms 𝓛 (∀' p ⟶ p[↦ₛ t]ₚ)
| a5 : Axioms 𝓛 (p ⟶ ∀' ↑ₚp)
| a6 : Axioms 𝓛 (∀' (p ⟶ q) ⟶ ∀' p ⟶ ∀' q)
| a7 : Axioms 𝓛 p → Axioms 𝓛 (∀' p)

inductive Proof (Γ : Formulas 𝓛) : Formula 𝓛 → Prop where
| assumption : p ∈ Γ → Proof Γ p
| axioms : p ∈ Axioms 𝓛 → Proof Γ p
| mp : Proof Γ (p ⟶ q) → Proof Γ p → Proof Γ q

infix:50 " ⊢ " => Proof

namespace Proof

elab "passumption_at " n:num : tactic => do
  Lean.Elab.Tactic.evalTactic $ ← `(tactic| apply Proof.assumption)
  for _ in [:n.getNat] do
    Lean.Elab.Tactic.evalTactic $ ← `(tactic| apply Or.inr)
  Lean.Elab.Tactic.evalTactic $ ← `(tactic| exact Or.inl rfl)

syntax "passumption" ("at" num)? : tactic
macro_rules
| `(tactic| passumption) => `(tactic| apply Proof.assumption; repeat (first | exact Or.inl rfl | apply Or.inr))
| `(tactic| passumption at $n) => `(tactic| passumption_at $n)

theorem mp2 : Γ ⊢ p ⟶ q ⟶ r → Γ ⊢ p → Γ ⊢ q → Γ ⊢ r :=
  λ h₁ h₂ h₃ => mp (mp h₁ h₂) h₃

theorem weaken : Γ ⊆ Δ → Γ ⊢ p → Δ ⊢ p := by
  intros h₁ h₂
  induction h₂ with
  | assumption h => exact assumption (h₁ h)
  | axioms h => exact axioms h
  | mp _ _ ih₁ ih₂ => exact mp ih₁ ih₂

theorem identity : Γ ⊢ p ⟶ p :=
  mp2 (axioms Axioms.a2) (axioms Axioms.a1) (axioms (Axioms.a1 (q := p)))

theorem deduction : Γ ⊢ p ⟶ q ↔ Γ,' p ⊢ q := by
  constructor
  · intro h
    apply mp
    · apply weaken
      · apply Set.subset_union_right
      · exact h
    · passumption
  · intro h
    induction h with
    | assumption h =>
      simp at h
      cases h with
      | inl h => cases h; apply identity
      | inr h => exact mp (axioms Axioms.a1) (assumption h)
    | axioms h => exact mp (axioms Axioms.a1) (axioms h)
    | mp _ _ ih₁ ih₂ => exact mp2 (axioms Axioms.a2) ih₁ ih₂

macro "pintro" : tactic => `(tactic| rw [deduction])
macro "pintros" : tactic => `(tactic| repeat pintro)

theorem composition : Γ ⊢ (p ⟶ q) ⟶ (q ⟶ r) ⟶ p ⟶ r := by
  pintros
  apply mp
  · passumption
  · apply mp <;> passumption

theorem contraposition : Γ ⊢ (p ⟶ q) ⟶ ~ q ⟶ ~ p := composition

theorem truth : Γ ⊢ ⊤ := identity

theorem explode : Γ ⊢ ⊥ ⟶ p := mp (axioms Axioms.a3) (mp (axioms Axioms.a1) truth)

theorem contradiction : Γ ⊢ ~ p ⟶ p ⟶ q := by
  pintros
  apply mp explode
  apply mp <;> passumption

theorem double_neg1 : Γ ⊢ p ⟶ ~ ~ p := by
  pintros
  apply mp <;> passumption

theorem double_neg2 : Γ ⊢ ~ ~ p ⟶ p := by
  pintro
  apply mp2 (axioms Axioms.a3)
  · pintros
    apply mp <;> passumption
  · passumption

theorem not_imp_left : Γ ⊢ ~ (p ⟶ q) ⟶ p := by
  pintro
  apply mp double_neg2
  apply mp2 contraposition
  · exact contradiction (q := q)
  · passumption

theorem not_imp_right : Γ ⊢ ~ (p ⟶ q) ⟶ ~ q := by
  apply mp contraposition
  exact Proof.axioms Axioms.a1

theorem and_intro : Γ ⊢ p ⟶ q ⟶ p ⋀ q := by
  pintros
  apply mp2 <;> passumption

theorem and_left : Γ ⊢ p ⋀ q ⟶ p := by
  pintro
  apply mp double_neg2
  pintro
  apply mp
  · passumption at 1
  · pintros
    apply mp <;> passumption

theorem and_right : Γ ⊢ p ⋀ q ⟶ q := by
  pintro
  apply mp double_neg2
  pintro
  apply mp
  · passumption at 1
  · pintro
    passumption

theorem or_inl : Γ ⊢ p ⟶ p ⋁ q := by
  pintros
  apply mp explode
  apply mp <;> passumption

theorem or_inr : Γ ⊢ q ⟶ p ⋁ q := by
  pintros
  passumption

theorem or_elim : Γ ⊢ p ⋁ q ⟶ (p ⟶ r) ⟶ (q ⟶ r) ⟶ r := by
  pintros
  apply mp double_neg2
  pintro
  apply mp; passumption
  apply mp; passumption at 2
  apply mp2 (axioms Axioms.a3)
  · apply mp2 composition; passumption
    apply mp2 composition
    · passumption
    · apply double_neg1
  · passumption

theorem excluded_middle : Γ ⊢ ~ p ⋁ p := double_neg2

theorem iff_intro : Γ ⊢ (p ⟶ q) ⟶ (q ⟶ p) ⟶ (p ⟷ q) := and_intro

theorem iff_left : Γ ⊢ (p ⟷ q) ⟶ (p ⟶ q) := and_left

theorem iff_right : Γ ⊢ (p ⟷ q) ⟶ (q ⟶ p) := and_right

theorem generalization : ↑ₚₛΓ ⊢ p → Γ ⊢ ∀' p := by
  intro h
  induction h with
  | assumption h =>
    rcases h with ⟨p, ⟨h₁, h₂⟩⟩
    subst h₂
    exact mp (axioms Axioms.a5) (assumption h₁)
  | axioms h => exact axioms (Axioms.a7 h)
  | mp _ _ ih₁ ih₂ => exact mp2 (axioms Axioms.a6) ih₁ ih₂

theorem not_forall : Γ ⊢ ~ ∀' p ⟶ ∃' (~ p) := by
  apply mp contraposition
  apply mp (axioms Axioms.a6)
  apply generalization
  apply weaken
  · apply Set.empty_subset
  · apply double_neg2

theorem not_exists : Γ ⊢ ~ ∃' p ⟶ ∀' (~ p) := double_neg2

theorem exists_intro : Γ ⊢ p[↦ₛ t]ₚ ⟶ ∃' p := by
  pintros
  suffices h : _ ⊢ (~ p)[↦ₛ t]ₚ by
    apply mp h
    passumption
  apply mp (axioms Axioms.a4)
  passumption

theorem exists_elim : Γ ⊢ ∃' p ⟶ (∀' (p ⟶ ↑ₚq)) ⟶ q := by
  pintros
  apply mp double_neg2
  pintros
  apply mp; passumption at 2
  suffices h : _ ⊢ ∀' (↑ₚ(~ q) ⟶ ~ p) by
    apply mp2 (axioms Axioms.a6) h
    apply mp (axioms Axioms.a5)
    passumption
  apply mp2 (axioms Axioms.a6)
  · apply generalization
    apply contraposition
  · passumption

theorem compactness : Γ ⊢ p → ∃ Δ, Δ ⊆ Γ ∧ Δ.Finite ∧ Δ ⊢ p := by
  intro h
  induction h with
  | @assumption p h =>
      exists {p}
      constructor
      · simp [h]
      constructor
      · simp
      · passumption; rfl
  | axioms h =>
      exists ∅
      constructor
      · simp
      constructor
      · simp
      · exact axioms h
  | mp _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨Δ₁, h₁, h₂, h₃⟩
      rcases ih₂ with ⟨Δ₂, h₄, h₅, h₆⟩
      exists Δ₁ ∪ Δ₂
      constructor
      · simp [h₁, h₄]
      constructor
      · simp [h₂, h₅]
      · apply Proof.mp
        · apply weaken
          · apply Set.subset_union_left
          · exact h₃
        · apply weaken
          · apply Set.subset_union_right
          · exact h₆

end Proof



infix:50 " ⊬ " => λ Γ p => ¬ Γ ⊢ p

def Consistent (Γ : Formulas 𝓛) := Γ ⊬ ⊥

theorem Consistent.weaken : Γ ⊆ Δ → Consistent Δ → Consistent Γ := by
  intros h₁ h₂ h
  apply h₂
  apply Proof.weaken
  · exact h₁
  · exact h

theorem Consistent.add : Consistent (Γ,' p) ↔ Γ ⊬ ~ p := by
  constructor
  · intro h₁ h₂
    apply h₁
    rw [←Proof.deduction]
    exact h₂
  · intro h₁ h₂
    apply h₁
    pintro
    exact h₂
