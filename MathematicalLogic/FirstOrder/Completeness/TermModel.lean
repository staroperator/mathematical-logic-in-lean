import MathematicalLogic.FirstOrder.Semantics
import MathematicalLogic.FirstOrder.Completeness.Basic

def Terms.ofVector : Vector (Term 𝓛) n → Terms 𝓛 n
| ⟨l, h⟩ =>
  match n, l with
  | 0, [] => []ₜ
  | n + 1, t :: l => t ∷ₜ Terms.ofVector ⟨l, by simp at h; exact h⟩

@[simp] lemma Terms.of_vector_nil : Terms.ofVector []ᵥ = ([]ₜ : Terms 𝓛 0) := rfl
@[simp] lemma Terms.of_vector_cons : Terms.ofVector (t ∷ᵥ v) = t ∷ₜ Terms.ofVector v := rfl

instance : Coe (Vector (Term 𝓛) n) (Terms 𝓛 n) where
  coe := Terms.ofVector

@[reducible] def TermModel (Γ : Context 𝓛) : Model 𝓛 where
  𝓤 := Term 𝓛
  𝓕 := λ f ts => f ⬝ₜ ts
  𝓟 := λ p ts => Γ ⊢ p ⬝ₚ ts

local notation "𝓜ᵀ" => TermModel

mutual
theorem Term.interp_term_model :
  ⟦ t ⟧ₜ 𝓜ᵀ Γ, ρ = t[ρ]ₜ :=
  match t with
  | #x => by simp
  | f ⬝ₜ ts => by simp; rw [Terms.interp_term_model]
theorem Terms.interp_term_model :
  (⟦ ts ⟧ₜₛ 𝓜ᵀ Γ, ρ : Terms 𝓛 n) = ts[ρ]ₜₛ :=
  match ts with
  | []ₜ => by simp
  | t ∷ₜ ts => by
    simp
    rw [Term.interp_term_model, Terms.interp_term_model]
    trivial
end

lemma subst_const {c : Const 𝓛} : (c : Term 𝓛)[σ]ₜ = c := rfl

lemma assignment_cons_in_term_model
  {Γ : Context 𝓛} {ρ : Assignment (TermModel Γ)} :
  ⇑ₛρ ∘ₛ ↦ₛ t = Assignment.cons (𝓜 := TermModel Γ) t ρ := by
  funext x
  cases x with
  | zero => rfl
  | succ x => simp [Subst.comp, Subst.lift, Term.shift_subst_single, Assignment.cons]

theorem Formula.interp_term_model :
  MaximalConsistent Γ → WitnessProperty Γ →
  (⟦ p ⟧ₚ 𝓜ᵀ Γ, ρ ↔ Γ ⊢ p[ρ]ₚ) := by
  rintro ⟨h₁, h₂⟩ h₃
  induction p generalizing ρ <;> simp
  case atom p ts => simp [Terms.interp_term_model]
  case false => exact h₁
  case imp p q ih₁ ih₂ =>
    rw [ih₁, ih₂]
    constructor
    · intro h
      rcases h₂ (p[ρ]ₚ) with h' | h'
      · exact Proof.mp (Proof.axioms Axioms.a1) (h h')
      · exact Proof.mp Proof.contradiction h'
    · exact Proof.mp
  case all p ih =>
    constructor
    · intro h₁'
      rcases h₂ (∀' p[⇑ₛρ]ₚ) with h₂' | h₂'
      · exact h₂'
      · exfalso
        apply Proof.mp Proof.not_forall at h₂'
        apply h₃ at h₂'
        rcases h₂' with ⟨c, h₂'⟩
        simp [Formula.subst, Formula.subst_comp] at h₂'
        rw [←subst_const (σ := ρ)] at h₂'
        apply h₁
        apply Proof.mp h₂'
        rw [←ih, assignment_cons_in_term_model]
        apply h₁'
    · intros h t
      apply Proof.mp (Proof.axioms (Axioms.a4 (t := t))) at h
      rw [Formula.subst_comp, ←ih, assignment_cons_in_term_model] at h
      exact h

theorem satisfiable_by_term_model :
  MaximalConsistent Γ → WitnessProperty Γ → Satisfiable Γ := by
  intros h₁ h₂
  apply Satisfiable.up.{0}
  exists 𝓜ᵀ Γ, Subst.id
  intros p h
  rw [Formula.interp_term_model h₁ h₂, Formula.subst_id]
  apply Proof.assumption
  exact h
