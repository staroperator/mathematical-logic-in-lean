import MathematicalLogic.FirstOrder.Completeness.Witness
import MathematicalLogic.FirstOrder.Completeness.Lindenbaum
import MathematicalLogic.FirstOrder.Completeness.TermModel

theorem model_existence : Consistent Γ → Satisfiable Γ := by
  intro h
  apply consistency_of_W at h
  apply lindenbaum at h
  rcases h with ⟨Δ, h₁, h₂⟩
  simp at h₁
  rcases h₁ with ⟨h₁, h₃⟩
  apply consts_keeps_satisfiability
  apply Satisfiable.weaken h₁
  apply satisfiable_by_term_model
  · exact h₂
  · apply witness_property_of_W
    exact h₃

theorem completeness : Γ ⊨ p → Γ ⊢ p := by
  intro h₁
  apply Proof.mp Proof.double_neg2
  by_contra h₂
  rw [←Consistent.add] at h₂
  apply model_existence at h₂
  rcases h₂ with ⟨𝓜, ρ, h₂⟩
  have h₃ := h₂ (~ p) (Set.mem_insert _ _)
  simp [Formula.interp_neg] at h₃
  apply h₃
  apply h₁
  intros q h
  apply h₂
  apply Set.mem_insert_of_mem
  exact h

theorem compactness : Γ ⊨ p → ∃ Δ, Δ ⊆ Γ ∧ Δ.Finite ∧ Δ ⊨ p := by
  intro h
  apply completeness at h
  apply Proof.compactness at h
  rcases h with ⟨Δ, h₁, h₂, h₃⟩
  apply soundness at h₃
  exists Δ
