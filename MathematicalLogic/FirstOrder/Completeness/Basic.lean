import MathematicalLogic.FirstOrder.Proof

def WitnessProperty (Γ : Context 𝓛) :=
  ∀ p, Γ ⊢ ∃' p → ∃ (c : Const 𝓛), Γ ⊢ p[↦ₛ c]ₚ

def MaximalConsistent (Γ : Context 𝓛) :=
  Consistent Γ ∧ ∀ p, Γ ⊢ p ∨ Γ ⊢ ~ p
