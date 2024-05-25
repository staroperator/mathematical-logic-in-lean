import MathematicalLogic.FirstOrder.Proof

namespace FirstOrder.Language.Context

variable {𝓛 : Language} (Γ : 𝓛.Context)

def Saturated := ∀ p, Γ ⊢ ∃' p → ∃ (c : 𝓛.Const), Γ ⊢ p[↦ₛ c]ₚ

def Complete := ∀ p, Γ ⊢ p ∨ Γ ⊢ ~ p

end FirstOrder.Language.Context
