import MathematicalLogic.FirstOrder.Semantics
import MathematicalLogic.FirstOrder.Proof

/-!

# Soundness of first-order logic

This file formalizes the soundness theorem of first-order logic.

-/

namespace FirstOrder.Language

variable {L : Language} {M : Type u} [L.HasStructure M] {n : ℕ} {Γ : L.FormulaSet n}
  {p q : L.Formula n}

theorem Entails.ax : p ∈ L.Axiom → Γ ⊨ p := by
  intro h M ρ _
  induction h with
  | forall_elim =>
    intro h
    rw [satisfy_subst_single]
    apply h
  | forall_self =>
    intro h _
    rw [satisfy_shift]
    exact h
  | eq_trans =>
    intro h₁ h₂
    rw [satisfy_eq] at h₁ h₂
    simp [h₁, h₂]
  | eq_congr_func | eq_congr_rel =>
    intro h
    simp only [satisfy_eq, satisfy_vecAnd] at h
    simp [h]
  | _ =>
    simp only [satisfy_eq, satisfy_imp, satisfy_neg, satisfy_all] <;> tauto

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

variable {T T₁ : L.Theory} [T.IsModel M] {p : L.Sentence}

theorem Theory.soundness : T ⊢ p → M ⊨ₛ p := by
  intro h
  apply Language.soundness h (M := .of M)
  exact IsModel.satisfy_theory

theorem Theory.IsModel.of_subtheory (T₂ : L.Theory) [T₁ ⊆ᵀ T₂] [IsModel T₂ M] : IsModel T₁ M where
  satisfy_theory _ h := T₂.soundness (Subtheory.subtheory _ h)

instance Theory.subtheory_theory : T ⊆ᵀ L.theory M :=
  .of_subset (λ _ h => soundness (.hyp h))

variable (M)

theorem Complete.provable_iff_satisfied (h : Complete T) : T ⊢ p ↔ M ⊨ₛ p := by
  by_cases h' : T ⊢ p
  · simpa [h'] using Theory.soundness h'
  · cases h p with
    | inl h => contradiction
    | inr h => simpa [h'] using Theory.soundness h

theorem Complete.theorems_eq_theory (h : Complete T) : T.theorems = L.theory M := by
  ext p
  exact h.provable_iff_satisfied M

variable (L)

theorem theory_consistent : Consistent (L.theory M) :=
  .of_satisfiable (theory_satisfiable L M)

theorem theory_complete : Complete (L.theory M) := by
  intro p
  by_cases h : M ⊨ₛ p
  · exact Or.inl (.hyp h)
  · exact Or.inr (.hyp h)

theorem theorems_theory_eq_theory : (L.theory M).theorems = L.theory M := by
  apply Theory.subset_theorems.antisymm'
  intro p h
  simpa [(theory_complete L M).provable_iff_satisfied M] using h

end FirstOrder.Language
