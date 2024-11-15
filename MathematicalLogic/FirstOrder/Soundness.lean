import MathematicalLogic.FirstOrder.Semantics
import MathematicalLogic.FirstOrder.Proof

namespace FirstOrder.Language

variable {𝓛 : Language}

theorem Entails.axioms : p ∈ 𝓛.Axioms → Γ ⊨ p := by
  intro h 𝓜 ρ _
  induction h <;> simp [Structure.interpFormula] <;> try tauto
  case forall_elim =>
    intro h
    simp [Structure.interpFormula_subst_single]
    apply h
  case forall_self =>
    intro h _
    simp [Structure.interpFormula_shift]
    exact h
  case eq_subst =>
    intro h₁ h₂
    simp [Structure.interpFormula_subst_single] at *
    rw [←h₁]; exact h₂

theorem Entails.mp : Γ ⊨.{u} p ⇒ q → Γ ⊨.{u} p → Γ ⊨.{u} q := by
  intros h₁ h₂ 𝓜 ρ h
  apply h₁
  · exact h
  · apply h₂; exact h

theorem soundness : Γ ⊢ p → Γ ⊨ p := by
  intro h
  induction h with
  | hyp h => intros _ _ h₁; apply h₁; exact h
  | ax h => exact Entails.axioms h
  | mp _ _ ih₁ ih₂ => exact Entails.mp ih₁ ih₂

theorem Consistent.of_satisfiable : Satisfiable Γ → Consistent Γ := by
  intro ⟨𝓜, ρ, h₁⟩ h₂
  apply soundness at h₂
  apply h₂
  exact h₁

theorem Consistent.empty : Consistent (∅ : 𝓛.FormulaSet n) := by
  apply of_satisfiable
  exists ⟨Unit, λ _ _ => (), λ _ _ => True⟩, λ _ => ()
  intro _ h
  contradiction

theorem Structure.theory.complete {𝓜 : 𝓛.Structure} : Complete 𝓜.theory := by
  intro p
  by_cases h : 𝓜 ⊨ₛ p
  · exact Or.inl (.hyp h)
  · exact Or.inr (.hyp h)

theorem Complete.provable_iff_satisfied {𝓣 : 𝓛.Theory} {𝓜 : 𝓣.Model} :
  Complete 𝓣 → (𝓣 ⊢ p ↔ 𝓜 ⊨ₛ p) := by
  intro h
  by_cases h' : 𝓣 ⊢ p <;> simp [h']
  · apply soundness h'; exact 𝓜.satisfy_theory
  · cases h p with
    | inl h => contradiction
    | inr h => apply soundness h; exact 𝓜.satisfy_theory

namespace Theory

theorem soundness {𝓣 : 𝓛.Theory} {𝓜 : 𝓣.Model} : 𝓣 ⊢ p → 𝓜 ⊨ₛ p := by
  intro h
  apply Language.soundness h
  apply 𝓜.satisfy_theory

abbrev theorems (𝓣 : 𝓛.Theory) : 𝓛.Theory := { p | 𝓣 ⊢ p }

abbrev Decidable (𝓣 : 𝓛.Theory) := DecidablePred 𝓣.theorems

theorem eq_theory_of_complete {𝓣 : 𝓛.Theory} {𝓜 : 𝓣.Model} :
  Complete 𝓣 → 𝓣.theorems = 𝓜.theory := by
  intro h
  ext p
  simp [Structure.theory]
  rw [h.provable_iff_satisfied]

end FirstOrder.Language.Theory
