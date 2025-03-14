import MathematicalLogic.FirstOrder.Semantics
import MathematicalLogic.FirstOrder.Proof

/-!

# Soundness of first-order logic

This file formalizes the soundness theorem of first-order logic.

-/

namespace FirstOrder.Language

variable {L : Language}

theorem Entails.ax : p ∈ L.Axiom → Γ ⊨ p := by
  intro h M ρ _
  induction h with simp [satisfy_andN]
  | forall_elim =>
    intro h
    simp [satisfy_subst_single]
    apply h
  | forall_self =>
    intro h _
    simp [satisfy_shift]
    exact h
  | eq_trans =>
    intro h₁ h₂; simp [h₁, h₂]
  | eq_congr_func | eq_congr_rel =>
    intro h; simp [h]
  | _ => tauto

theorem Entails.mp : Γ ⊨.{u} p ⇒ q → Γ ⊨.{u} p → Γ ⊨.{u} q := by
  intros h₁ h₂ M ρ h
  apply h₁
  · exact h
  · apply h₂; exact h

/-- Soundness theorem. -/
theorem soundness : Γ ⊢ p → Γ ⊨ p := by
  intro h
  induction h with
  | hyp h => intros _ _ h₁; apply h₁; exact h
  | ax h => exact Entails.ax h
  | mp _ _ ih₁ ih₂ => exact Entails.mp ih₁ ih₂

theorem Consistent.of_satisfiable : Satisfiable Γ → Consistent Γ := by
  intro ⟨M, ρ, h₁⟩ h₂
  apply soundness at h₂
  apply h₂
  exact h₁

theorem Consistent.empty : Consistent (∅ : L.FormulaSet n) :=
  of_satisfiable.{0} .empty

variable {T : L.Theory} {M : Type u} [L.IsStructure M] [T.IsModel M]

theorem theory.complete : Complete (L.theory M) := by
  intro p
  by_cases h : M ⊨ₛ p
  · exact Or.inl (.hyp h)
  · exact Or.inr (.hyp h)

theorem theory.consistent : Consistent (L.theory M) :=
  .of_satisfiable satisfiable

namespace Theory

theorem soundness : T ⊢ p → M ⊨ₛ p := by
  intro h
  apply Language.soundness h (M := .of M)
  exact IsModel.satisfy_theory

theorem IsModel.of_subtheory (T₂ : L.Theory) [T₁ ⊆ᵀ T₂] [IsModel T₂ M] : IsModel T₁ M where
  satisfy_theory _ h := T₂.soundness (Subtheory.subtheory _ h)

instance subtheory_theory : T ⊆ᵀ L.theory M :=
  .of_subset (λ _ h => soundness (.hyp h))

end Theory

theorem Complete.provable_iff_satisfied (h : Complete T) : T ⊢ p ↔ M ⊨ₛ p := by
  by_cases h' : T ⊢ p <;> simp [h']
  · exact Theory.soundness h'
  · cases h p with
    | inl h => contradiction
    | inr h => apply Theory.soundness h

theorem Complete.eq_theory (h : Complete T) : T.theorems = L.theory M := by
  ext p
  simp [theory]
  exact h.provable_iff_satisfied

end FirstOrder.Language
