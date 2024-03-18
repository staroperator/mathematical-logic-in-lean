import Mathlib.Data.Set.Basic
import Mathlib.Order.Zorn
import MathematicalLogic.FirstOrder.Proof
import MathematicalLogic.FirstOrder.Completeness.Basic

lemma consistent_chain_upper_bound
  (S : Set (Set (Formula 𝓛))) :
  (∀ Γ ∈ S, Consistent Γ) →
  IsChain Set.Subset S →
  Set.Nonempty S →
  ∃ Γ, Consistent Γ ∧ ∀ Δ ∈ S, Δ ⊆ Γ := by
  intros h₁ h₂ h₃
  exists ⋃₀ S
  constructor
  · intro h₄
    rcases Proof.compactness h₄ with ⟨Γ, h₁', h₂', h₃'⟩
    have h : ∃ Δ ∈ S, Γ ⊆ Δ := by
      apply Set.Finite.induction_on' (C := λ Γ => ∃ Δ ∈ S, Γ ⊆ Δ) h₂'
      · rcases h₃ with ⟨Δ, h₃⟩
        exists Δ
        constructor <;> simp [h₃]
      · rintro p Δ' h₁'' _ _ ⟨Δ, h₂'', h₃''⟩
        apply h₁' at h₁''
        simp at h₁''
        rcases h₁'' with ⟨Γ, h₆'', h₇''⟩
        have : ∀ {α}, IsRefl (Set α) Set.Subset := ⟨λ _ _ => id⟩
        rcases h₂.total h₆'' h₂'' with (h | h)
        · exists Δ
          constructor
          · exact h₂''
          · apply Set.insert_subset
            · exact h h₇''
            · exact h₃''
        · exists Γ
          constructor
          · exact h₆''
          · apply Set.insert_subset
            · exact h₇''
            · exact Set.Subset.trans h₃'' h
    rcases h with ⟨Δ, h, h'⟩
    apply h₁ at h
    apply Consistent.weaken h' at h
    contradiction
  · intro Δ h
    apply Set.subset_sUnion_of_mem
    exact h

theorem lindenbaum :
  Consistent Γ → ∃ Δ, Γ ⊆ Δ ∧ MaximalConsistent Δ := by
  intro h
  apply zorn_subset_nonempty _ consistent_chain_upper_bound at h
  rcases h with ⟨Δ, h₁, h₂, h₃⟩
  exists Δ
  constructor
  · exact h₂
  · constructor
    · exact h₁
    · intro p
      by_contra h
      simp [not_or] at h
      rcases h with ⟨h, h'⟩
      rw [←Consistent.add] at h'
      replace h' := h₃ _ h' (Set.subset_insert _ _)
      simp [Context.append, Set.insert_eq_self] at h'
      apply h
      apply Proof.assumption
      exact h'
