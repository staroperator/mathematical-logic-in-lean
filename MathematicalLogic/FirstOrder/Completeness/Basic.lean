import MathematicalLogic.FirstOrder.Proof

def WitnessProperty (Γ : Context 𝓛) :=
  ∀ p, Γ ⊢ ∃' p → ∃ t, Γ ⊢ p[↦ₛ t]ₚ

def MaximalConsistent (Γ : Context 𝓛) :=
  Consistent Γ ∧ ∀ p, Γ ⊢ p ∨ Γ ⊢ ~ p
