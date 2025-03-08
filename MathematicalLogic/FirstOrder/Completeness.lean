import MathematicalLogic.FirstOrder.Soundness
import MathematicalLogic.FirstOrder.Completeness.Henkin
import MathematicalLogic.FirstOrder.Completeness.Lindenbaum
import MathematicalLogic.FirstOrder.Completeness.TermModel

/-!

# Completeness of first-order logic

This file formalizes the completeness theorem (also referred as Godel's completeness theorem) of
first-order logic.

The proof mainly follows [flypitch](https://github.com/flypitch/flypitch):

1. We first prove that any theory can be extended with Henkin constants and Henkin axioms while
  keeping its consistency (`FormulaSet.henkinStep`).
2. We then prove that starting from a consistent theory, extends it with Henkin constants ω times
  creates a consistent theory that satisfies Henkin property (`FormulaSet.henkinize`).
3. We show the Lindenbaum's theorem: any consistent theory can be extended to a consistent, complete
  theory (`FormulaSet.lindenbaum`).
4. Finally we show that a consistent, complete theory satisfying Henkin property is satisfiable by
  its syntactic terms (`FormulaSet.TermModel`).

This file collects the main results only; the details are decomposed into files under `Completeness`
folder (`Language.lean`, `Henkin.lean`, `Lindenbaum.lean` and `TermModel.lean`).

## References

* flypitch. <https://github.com/flypitch/flypitch>

-/

namespace FirstOrder.Language

variable {L : Language} {Γ : L.FormulaSet n}

theorem Satisfiable.of_consistent : Consistent Γ → Satisfiable Γ := by
  intro h₁
  by_cases h : Γ ⊢ ∃' ⊤
  · apply FormulaSet.henkinize.consistent h at h₁
    apply FormulaSet.lindenbaum at h₁
    rcases h₁ with ⟨Δ, h₁, h₂, h₃⟩
    have := FormulaSet.TermModel.satisfiable h₂ h₃ (FormulaSet.henkinize.supset_henkin h₁)
    apply Satisfiable.weaken h₁ at this
    apply Satisfiable.weaken (Set.subset_iUnion _ 0) at this
    exact Hom.on_satisfiable this
  · rw [←Consistent.append_neg] at h
    apply FormulaSet.lindenbaum at h
    rcases h with ⟨Δ, h₂, h₃, h₄⟩
    refine Satisfiable.weaken (Set.Subset.trans (Set.subset_insert _ _) h₂) (FormulaSet.TermModel.satisfiable h₃ h₄ ?_)
    intro p h
    exfalso; apply h₃
    have : Δ ⊢ ~ ∃' ⊤ := by apply Proof.weaken h₂; passumption
    papply this
    papply Proof.exists_imp (p := p)
    · apply Proof.forall_intro; pintro; exact Proof.true_intro
    · exact h

theorem consistent_iff_satisfiable : Consistent Γ ↔ Satisfiable Γ := ⟨Satisfiable.of_consistent, Consistent.of_satisfiable⟩

/-- Completeness theorem. -/
theorem completeness : Γ ⊨ p → Γ ⊢ p := by
  intro h₁
  papply Proof.double_neg_imp
  by_contra h₂
  rw [←Consistent.append] at h₂
  apply Satisfiable.of_consistent at h₂
  rcases h₂ with ⟨M, ρ, h₂⟩
  have h₃ := h₂ (~ p) (Set.mem_insert _ _)
  apply h₃
  apply h₁
  intros q h
  apply h₂
  exact Set.mem_insert_of_mem _ h

theorem provable_iff_entails : Γ ⊢ p ↔ Γ ⊨ p := ⟨soundness, completeness⟩

theorem Entails.compactness : Γ ⊨ p → ∃ Δ, Δ ⊆ Γ ∧ Δ.Finite ∧ Δ ⊨ p := by
  intro h
  apply completeness at h
  apply Proof.compactness at h
  rcases h with ⟨Δ, h₁, h₂, h₃⟩
  apply soundness at h₃
  exists Δ

/-- Compactness theorem. -/
theorem Satisfiable.compactness : Satisfiable.{u} Γ ↔ ∀ Δ ⊆ Γ, Δ.Finite → Satisfiable.{u} Δ := by
  constructor
  · intros; apply weaken <;> assumption
  · intro h
    rw [←consistent_iff_satisfiable]
    intro h₁
    apply Proof.compactness at h₁
    rcases h₁ with ⟨Δ, h₁, h₂, h₃⟩
    have h₄ := h Δ h₁ h₂
    rw [←consistent_iff_satisfiable] at h₄
    contradiction

theorem Theory.complete_iff_elementary_equivalent {T : L.Theory} :
  Complete T ↔ ∀ (M : T.Model) (N : T.Model), M ≃ᴱ (N : L.Structure) := by
  constructor
  · intro h M N p
    cases h p with
    | inl h₁ => simp [soundness h₁]
    | inr h₁ => rw [←not_iff_not]; simp [←satisfy_neg, soundness h₁]
  · intro h p
    by_contra h₁; rw [not_or] at h₁; rcases h₁ with ⟨h₁, h₂⟩
    rw [←Consistent.append_neg] at h₁; apply Satisfiable.of_consistent at h₁
    rw [satisfiable_iff] at h₁; rcases h₁ with ⟨⟨M, h₁⟩⟩
    have h₁' := h₁ (~ p) (Or.inl rfl)
    simp [←Consistent.append] at h₂; apply Satisfiable.of_consistent at h₂
    rw [satisfiable_iff] at h₂; rcases h₂ with ⟨⟨N, h₂⟩⟩
    have h₂' := h₂ p (Or.inl rfl)
    have h₃ := h ⟨M, λ p h => h₁ p (Or.inr h)⟩ ⟨N, λ p h => h₂ p (Or.inr h)⟩ p
    simp at h₃; simp [←h₃] at h₂'
    contradiction

end FirstOrder.Language
