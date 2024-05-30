import MathematicalLogic.FirstOrder.Theory
import MathematicalLogic.FirstOrder.Completeness.Henkin
import MathematicalLogic.FirstOrder.Completeness.Lindenbaum
import MathematicalLogic.FirstOrder.Completeness.TermModel

namespace FirstOrder.Language

variable {𝓛 : Language} {Γ : 𝓛.Context}

theorem Context.Satisfiable.of_consistent : Γ.Consistent → Γ.Satisfiable := by
  intro h
  apply consistency_of_henkin_formulas at h
  apply lindenbaum at h
  rcases h with ⟨Δ, h₁, h₂, h₃⟩
  simp at h₁; rcases h₁ with ⟨h₁, h₁'⟩
  apply consts_keeps_satisfiability (𝓒 := 𝓛.witOmega)
  apply Satisfiable.weaken h₁
  apply satisfiable_by_term_model h₂ h₃
  exact henkin_formulas_saturated h₁'

theorem Context.consistent_iff_satisfiable : Γ.Consistent ↔ Γ.Satisfiable := ⟨Satisfiable.of_consistent, Consistent.of_satisfiable⟩

theorem completeness : Γ ⊨ p → Γ ⊢ p := by
  intro h₁
  apply Proof.mp Proof.double_neg2
  by_contra h₂
  rw [←Context.Consistent.append] at h₂
  apply Context.Satisfiable.of_consistent at h₂
  rcases h₂ with ⟨𝓜, ρ, h₂⟩
  have h₃ := h₂ (~ p) (Set.mem_insert _ _)
  simp [Formula.interp_neg] at h₃
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

theorem Context.Satisfiable.compatcness : Satisfiable.{u} Γ ↔ ∀ Δ ⊆ Γ, Δ.Finite → Satisfiable.{u} Δ := by
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

variable {𝓣 : 𝓛.Theory}

theorem Theory.Satisfiable.of_consistent : 𝓣.Consistent → 𝓣.Satisfiable := by
  intro h
  apply Context.Satisfiable.of_consistent at h
  rcases h with ⟨𝓢, ρ, h⟩
  exists 𝓢
  intros p h'
  rw [Sentence.val_interp_eq]
  apply h
  exists p

theorem Theory.consistent_iff_satisfiable : 𝓣.Consistent ↔ 𝓣.Satisfiable := ⟨Satisfiable.of_consistent, Consistent.of_satisfiable⟩

theorem Theory.complete_iff_elementary_equivalent :
  𝓣.Complete ↔ ∀ (𝓜 𝓝 : 𝓣.Model), 𝓜 ≃ᴱ (𝓝 : 𝓛.Structure) := by
  constructor
  · intro h 𝓜 𝓝 p
    cases h p with
    | inl h₁ => simp [soundness' h₁]
    | inr h₁ => rw [←not_iff_not]; simp [←Sentence.interp_neg, soundness' h₁]
  · intro h p
    by_contra h₁; rw [not_or] at h₁; rcases h₁ with ⟨h₁, h₂⟩
    rw [←Context.Consistent.append'] at h₁
    apply Context.Satisfiable.of_consistent at h₁
    rcases h₁ with ⟨𝓜, _, h₁⟩
    have h₁' := h₁ (~ p).val (Or.inl rfl)
    rw [←Sentence.val_interp_eq] at h₁'
    simp [←Context.Consistent.append] at h₂
    apply Context.Satisfiable.of_consistent at h₂
    rcases h₂ with ⟨𝓝, _, h₂⟩
    have h₂' := h₂ p.val (Or.inl rfl)
    rw [←Sentence.val_interp_eq] at h₂'
    have h₃ := h ⟨𝓜, by intros p _; rw [Sentence.val_interp_eq]; apply h₁; right; exists p⟩
      ⟨𝓝, by intros p _; rw [Sentence.val_interp_eq]; apply h₂; right; exists p⟩ p
    simp at h₃
    rw [←h₃] at h₂'
    contradiction

end FirstOrder.Language
