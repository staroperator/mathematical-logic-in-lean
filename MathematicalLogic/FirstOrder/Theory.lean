import MathematicalLogic.FirstOrder.Semantics
import MathematicalLogic.FirstOrder.Bounded

universe u

@[reducible] def Theory (𝓛) := Set (Sentence 𝓛)

def Theory.context (𝓣 : Theory 𝓛) : Context 𝓛 := { ↑p | p ∈ 𝓣 }

lemma Theory.shift_eq {𝓣 : Theory 𝓛} : ↑ₚₛ𝓣.context = 𝓣.context := by
  unfold context
  simp [Context.lift, Sentence.shift_eq]

notation 𝓣:50 " ⊢ᵀ " p:50 => Theory.context 𝓣 ⊢ p

theorem Theory.generalization {𝓣 : Theory 𝓛} :
  𝓣 ⊢ᵀ p → 𝓣 ⊢ᵀ ∀' p := by
  intro h
  apply Proof.generalization
  rw [Theory.shift_eq]
  exact h

def Theory.model (𝓣 : Theory 𝓛) : Type (u + 1) :=
  { 𝓜 : Model 𝓛 | ∀ p ∈ 𝓣, ⟦ p ⟧ₛ 𝓜 }

instance {𝓣 : Theory 𝓛} : CoeOut (𝓣.model) (Model 𝓛) where
  coe := Subtype.val

theorem Theory.model_satisfies_context
  {𝓣 : Theory 𝓛} {𝓜 : 𝓣.model} {ρ : Assignment 𝓜} :
  p ∈ 𝓣.context → ⟦ p ⟧ₚ 𝓜, ρ := by
  rintro ⟨p, h₁, h₂⟩
  subst h₂
  simp [←Sentence.unbounded_interp_eq]
  apply 𝓜.property
  exact h₁
