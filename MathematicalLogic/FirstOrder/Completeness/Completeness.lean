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

theorem compactness : Γ ⊨ p → ∃ Δ, Δ ⊆ Γ ∧ Δ.Finite ∧ Δ ⊨ p := by
  intro h
  apply completeness at h
  apply Proof.compactness at h
  rcases h with ⟨Δ, h₁, h₂, h₃⟩
  apply soundness at h₃
  exists Δ

theorem Theory.Satisfiable.of_consistent {𝓣 : 𝓛.Theory} :
  𝓣.Consistent → 𝓣.Satisfiable := by
  intro h
  apply Context.Satisfiable.of_consistent at h
  rcases h with ⟨𝓢, ρ, h⟩
  exists 𝓢
  intros p h'
  rw [Sentence.val_interp_eq]
  apply h
  exists p

end FirstOrder.Language
