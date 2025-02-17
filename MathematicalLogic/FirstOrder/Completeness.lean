import MathematicalLogic.FirstOrder.Soundness
import MathematicalLogic.FirstOrder.Completeness.Henkin
import MathematicalLogic.FirstOrder.Completeness.Lindenbaum
import MathematicalLogic.FirstOrder.Completeness.TermModel

namespace FirstOrder.Language

variable {𝓛 : Language} {Γ : 𝓛.FormulaSet n}

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

theorem completeness : Γ ⊨ p → Γ ⊢ p := by
  intro h₁
  papply Proof.double_neg_imp
  by_contra h₂
  rw [←Consistent.append] at h₂
  apply Satisfiable.of_consistent at h₂
  rcases h₂ with ⟨𝓜, ρ, h₂⟩
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

theorem Theory.complete_iff_elementary_equivalent {𝓣 : 𝓛.Theory} :
  Complete 𝓣 ↔ ∀ (𝓜 : 𝓣.Model) (𝓝 : 𝓣.Model), 𝓜 ≃ᴱ (𝓝 : 𝓛.Structure) := by
  constructor
  · intro h 𝓜 𝓝 p
    cases h p with
    | inl h₁ => simp [soundness h₁]
    | inr h₁ => rw [←not_iff_not]; simp [←Structure.satisfy_neg, soundness h₁]
  · intro h p
    by_contra h₁; rw [not_or] at h₁; rcases h₁ with ⟨h₁, h₂⟩
    rw [←Consistent.append_neg] at h₁; apply Satisfiable.of_consistent at h₁
    rw [satisfiable_iff] at h₁; rcases h₁ with ⟨⟨𝓜, h₁⟩⟩
    have h₁' := h₁ (~ p) (Or.inl rfl)
    simp [←Consistent.append] at h₂; apply Satisfiable.of_consistent at h₂
    rw [satisfiable_iff] at h₂; rcases h₂ with ⟨⟨𝓝, h₂⟩⟩
    have h₂' := h₂ p (Or.inl rfl)
    have h₃ := h ⟨𝓜, λ p h => h₁ p (Or.inr h)⟩ ⟨𝓝, λ p h => h₂ p (Or.inr h)⟩ p
    simp at h₃; simp [←h₃] at h₂'
    contradiction

end FirstOrder.Language
