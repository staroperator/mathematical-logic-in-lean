import Mathlib.Data.Fintype.Quotient
import MathematicalLogic.FirstOrder.Proof
import MathematicalLogic.FirstOrder.Semantics

def Quotient.liftOnVec {s : Setoid α} (v : Vec (Quotient s) n) (f : Vec α n → β)
  (h : (v₁ v₂ : Vec α n) → (∀ i, v₁ i ≈ v₂ i) → f v₁ = f v₂) : β :=
  Quotient.liftOn (Quotient.finChoice v) f h

theorem Quotient.liftOnVec_mk {s : Setoid α} {f : Vec α n → β} {h} :
  liftOnVec (s := s) (λ i => ⟦v i⟧) f h = f v := by
  simp [liftOnVec, Quotient.finChoice_eq, Quotient.liftOn_mk]

namespace FirstOrder.Language.FormulaSet

variable {𝓛 : Language}

def TermSetoid (Γ : 𝓛.FormulaSet n) : Setoid (𝓛.Term n) where
  r t₁ t₂ := Γ ⊢ t₁ ≐ t₂
  iseqv.refl _ := Proof.eq_refl
  iseqv.symm := Proof.eq_symm.mp
  iseqv.trans := Proof.eq_trans.mp₂

@[simps] def TermModel (Γ : 𝓛.FormulaSet n) : 𝓛.Structure where
  Dom := Quotient (TermSetoid Γ)
  interpFunc f v :=
    Quotient.liftOnVec v (⟦f ⬝ₜ ·⟧)
      (by intros v₁ v₂ h; simp; papply Proof.eq_congr_func; exact Proof.andN_intro h)
  interpRel r v :=
    Quotient.liftOnVec v (Γ ⊢ r ⬝ᵣ ·)
      (by intros v₁ v₂ h; simp; apply Proof.iff_iff; papply Proof.eq_congr_rel_iff; exact Proof.andN_intro h)

namespace TermModel

variable {Γ : 𝓛.FormulaSet n} {σ : 𝓛.Subst m n}

theorem interp_term : ⟦ t ⟧ₜ Γ.TermModel, (⟦σ ·⟧) = ⟦t[σ]ₜ⟧ := by
  induction t with simp [Structure.interpTerm]
  | func f v ih => simp [ih, Quotient.liftOnVec_mk]

variable (h₁ : Consistent Γ) (h₂ : Complete Γ) (h₃ : Henkin Γ)
include h₁ h₂ h₃

theorem interp_formula : Γ.TermModel ⊨[(⟦σ ·⟧)] p ↔ Γ ⊢ p[σ]ₚ := by
  induction p generalizing n with simp [Structure.interpFormula]
  | rel r v => simp [interp_term, Quotient.liftOnVec_mk]
  | eq t₁ t₂ => simp [interp_term]; rfl
  | false => exact h₁
  | imp p q ih₁ ih₂ =>
    rw [ih₁ h₁ h₂ h₃, ih₂ h₁ h₂ h₃]
    constructor
    · intro h
      rcases h₂ (p[σ]ₚ) with h' | h'
      · pintro; pexact h h'
      · papply Proof.contradiction; exact h'
    · exact Proof.mp
  | all p ih =>
    constructor
    · intro h₁'
      rcases h₂ (∀' p[⇑ₛσ]ₚ) with h₂' | h₂'
      · exact h₂'
      · exfalso
        apply Proof.iff_mp.mp₂ Proof.not_forall_iff at h₂'
        apply h₃ at h₂'
        rcases h₂' with ⟨c, h₂'⟩
        simp at h₂'; rw [←Term.subst_const (σ := σ), ←Formula.subst_swap_single, ←Formula.subst_comp] at h₂'
        apply h₁
        apply h₂'.mp
        rw [←ih h₁ h₂ h₃]
        have : (λ x => ⟦(↦ₛ c ∘ₛ σ) x⟧) = (⟦c⟧ : Quotient (TermSetoid Γ)) ∷ᵥ (⟦σ ·⟧) := by
          funext x; cases x using Fin.cases <;> simp [Vec.eq_nil]
        rw [this]
        apply h₁'
    · rintro h ⟨t⟩
      apply (Proof.forall_elim (t := t)).mp at h
      rw [←Formula.subst_comp, ←ih h₁ h₂ h₃] at h
      have : (λ x => ⟦(⇑ₛσ ∘ₛ ↦ₛ t) x⟧) = (⟦t⟧ : Quotient (TermSetoid Γ)) ∷ᵥ (⟦σ ·⟧) := by
        funext x; cases x using Fin.cases <;> simp [Term.shift_subst_single]
      rw [this] at h
      exact h

theorem satisfiable : Satisfiable Γ := by
  apply Satisfiable.up.{0}
  exists TermModel Γ, (⟦Subst.id ·⟧)
  intros p h
  rw [interp_formula h₁ h₂ h₃, Formula.subst_id]
  exact Proof.hyp h

end FirstOrder.Language.FormulaSet.TermModel
