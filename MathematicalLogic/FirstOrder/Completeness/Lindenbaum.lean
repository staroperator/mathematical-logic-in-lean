import Mathlib.Order.Zorn
import MathematicalLogic.FirstOrder.Proof

namespace FirstOrder.Language.FormulaSet

variable {𝓛 : Language}

lemma consistent_chain_upper_bound (S : Set (𝓛.FormulaSet n))
  (h₁ : ∀ Γ ∈ S, Consistent Γ) (h₂ : IsChain Set.Subset S) (h₃ : S.Nonempty) :
  ∃ Γ, Consistent Γ ∧ ∀ Δ ∈ S, Δ ⊆ Γ := by
  exists ⋃₀ S
  constructor
  · intro h₄
    rcases Proof.compactness h₄ with ⟨Γ, h₁', h₂', h₃'⟩
    have h : ∃ Δ ∈ S, Γ ⊆ Δ := by
      clear h₃'
      induction Γ, h₂' using Set.Finite.induction_on_subset with
      | empty =>
        rcases h₃ with ⟨Δ, h₃⟩
        exists Δ
        constructor <;> simp [h₃]
      | @insert p Δ h₂' _ _ h₃' =>
        simp [Set.insert_subset_iff] at h₁'
        rcases h₁' with ⟨⟨Δ₁, h₁'', h₂''⟩, h₁'⟩
        apply h₃' at h₁'
        rcases h₁' with ⟨Δ₂, h₃'', h₄''⟩
        have : ∀ {α}, IsRefl (Set α) Set.Subset := ⟨λ _ _ => id⟩
        rcases h₂.total h₁'' h₃'' with (h | h)
        · exists Δ₂
          constructor
          · exact h₃''
          · apply Set.insert_subset
            · exact h h₂''
            · exact h₄''
        · exists Δ₁
          constructor
          · exact h₁''
          · apply Set.insert_subset
            · exact h₂''
            · exact h₄''.trans h
    rcases h with ⟨Δ, h, h'⟩
    apply h₁ at h
    apply Consistent.weaken h' at h
    contradiction
  · intro Δ h
    apply Set.subset_sUnion_of_mem
    exact h

theorem lindenbaum (Γ : 𝓛.FormulaSet n) (h : Consistent Γ) :
  ∃ Δ, Γ ⊆ Δ ∧ Consistent Δ ∧ Complete Δ := by
  apply zorn_subset_nonempty _ consistent_chain_upper_bound at h
  rcases h with ⟨Δ, h₁, h₂, h₃⟩
  exists Δ, h₁, h₂
  intro p
  by_contra h; simp at h; rcases h with ⟨h, h'⟩
  rw [←Consistent.append] at h'
  apply h
  apply Proof.hyp
  apply h₃ h' <;> simp [FormulaSet.mem_append, FormulaSet.subset_append]

end FirstOrder.Language.FormulaSet
