import Mathlib.Data.Vector
import MathematicalLogic.FirstOrder.Proof

universe u

structure Model (𝓛 : Language) where
  𝓤 : Type u
  𝓕 : 𝓛.𝓕 n → Vector 𝓤 n → 𝓤
  𝓟 : 𝓛.𝓟 n → Vector 𝓤 n → Prop

def Assignment (𝓜: Model 𝓛) := ℕ → 𝓜.𝓤

def Assignment.cons (u : 𝓜.𝓤) (ρ : Assignment 𝓜) : Assignment 𝓜
| 0 => u
| x + 1 => ρ x

infixr:80 " ∷ₐ " => Assignment.cons

mutual
def Term.interp : Term 𝓛 → (𝓜 : Model 𝓛) → Assignment 𝓜 → 𝓜.𝓤
| #x, _, ρ => ρ x
| f ⬝ₜ ts, 𝓜, ρ => 𝓜.𝓕 f (ts.interp 𝓜 ρ)
def Terms.interp : Terms 𝓛 n → (𝓜 : Model 𝓛) → Assignment 𝓜 → Vector 𝓜.𝓤 n
| []ₜ, _, _ => Vector.nil
| t ∷ₜ ts, 𝓜, ρ => Vector.cons (t.interp 𝓜 ρ) (ts.interp 𝓜 ρ)
end
termination_by
  Term.interp t _ _ => t.size
  Terms.interp ts _ _ => ts.size

notation:80 "⟦" t "⟧ₜ " 𝓜 ", " ρ:80 => Term.interp t 𝓜 ρ
notation:80 "⟦" ts "⟧ₜₛ " 𝓜 ", " ρ:80 => Terms.interp ts 𝓜 ρ

def Assignment.subst {𝓜 : Model 𝓛} (ρ : Assignment 𝓜) (σ : Subst 𝓛) : Assignment 𝓜
  := λ x => ⟦ σ x ⟧ₜ 𝓜, ρ

notation:80 ρ "[" σ "]ₐ" => Assignment.subst ρ σ

lemma Assignment.subst_shift {ρ : Assignment 𝓜} : (u ∷ₐ ρ)[Subst.shift]ₐ = ρ := by
  funext x
  simp [Assignment.subst, Subst.shift, Term.interp, Assignment.cons]

lemma Assignment.subst_single {ρ : Assignment 𝓜} : ρ[↦ₛ t]ₐ = (⟦ t ⟧ₜ 𝓜, ρ) ∷ₐ ρ := by
  funext x
  cases x with
  | zero => rfl
  | succ => simp [Assignment.subst, Subst.single, Term.interp, Assignment.cons]

mutual
theorem Term.interp_subst : ⟦ t[σ]ₜ ⟧ₜ 𝓜, ρ = ⟦ t ⟧ₜ 𝓜, ρ[σ]ₐ := match t with
| #x => by simp [Term.interp, Assignment.subst]
| f ⬝ₜ ts => by simp [Term.interp]; rw [Terms.interp_subst]
theorem Terms.interp_subst : ⟦ ts[σ]ₜₛ ⟧ₜₛ 𝓜, ρ = ⟦ ts ⟧ₜₛ 𝓜, ρ[σ]ₐ := match ts with
| []ₜ => by rfl
| t ∷ₜ ts => by simp [Terms.interp]; rw [Term.interp_subst, Terms.interp_subst]
end
termination_by
  Term.interp_subst _ t _ _ _ => t.size
  Terms.interp_subst _ _ ts _ _ _ => ts.size



def Formula.interp : Formula 𝓛 → (𝓜 : Model 𝓛) → Assignment 𝓜 → Prop
| p ⬝ₚ ts, 𝓜, ρ => 𝓜.𝓟 p (⟦ ts ⟧ₜₛ 𝓜, ρ)
| ⊥, _, _ => False
| p ⟶ q, 𝓜, ρ => p.interp 𝓜 ρ → q.interp 𝓜 ρ
| ∀' p, 𝓜, ρ => ∀ u, p.interp 𝓜 (u ∷ₐ ρ)

notation:80 "⟦" p "⟧ₚ " 𝓜 ", " ρ:80 => Formula.interp p 𝓜 ρ

theorem Formula.interp_subst : ⟦ p[σ]ₚ ⟧ₚ 𝓜, ρ = ⟦ p ⟧ₚ 𝓜, ρ[σ]ₐ := by
  induction p generalizing ρ σ with
  | atom => simp [Formula.interp, Terms.interp_subst]
  | false => rfl
  | implies _ _ ih₁ ih₂ => simp [Formula.interp, ih₁, ih₂]
  | all _ ih =>
      rw [Formula.interp]
      apply forall_congr
      intro u
      rw [ih]
      congr
      funext x
      cases x
      · rfl
      · simp [Assignment.subst, Subst.lift, Term.shift]
        conv => lhs; simp [Term.interp_subst, Assignment.subst_shift]

theorem Formula.interp_neg : ⟦ ~ p ⟧ₚ 𝓜, ρ = ¬ ⟦ p ⟧ₚ 𝓜, ρ
  := by simp [Formula.interp]

theorem Formula.interp_and : ⟦ p ⋀ q ⟧ₚ 𝓜, ρ = (⟦ p ⟧ₚ 𝓜, ρ ∧ ⟦ q ⟧ₚ 𝓜, ρ)
  := by simp [Formula.interp, imp_false]

theorem Formula.interp_or : ⟦ p ⋁ q ⟧ₚ 𝓜, ρ = (⟦ p ⟧ₚ 𝓜, ρ ∨ ⟦ q ⟧ₚ 𝓜, ρ)
  := by simp [Formula.interp, imp_iff_not_or]

theorem Formula.interp_iff : ⟦ p ⟷ q ⟧ₚ 𝓜, ρ = (⟦ p ⟧ₚ 𝓜, ρ ↔ ⟦ q ⟧ₚ 𝓜, ρ)
  := by simp [Formula.interp, imp_false, iff_iff_implies_and_implies]

theorem Formula.interp_exists : ⟦ ∃' p ⟧ₚ 𝓜, ρ = ∃ u, ⟦ p ⟧ₚ 𝓜, u ∷ₐ ρ
  := by simp [Formula.interp, imp_false]



def Entails (Γ : Formulas 𝓛) (p)
  := ∀ (𝓜 : Model.{u} 𝓛) (ρ : Assignment 𝓜), (∀ q ∈ Γ, ⟦ q ⟧ₚ 𝓜, ρ) → ⟦ p ⟧ₚ 𝓜, ρ

infix:50 " ⊨ " => Entails
syntax:50 term " ⊨.{" level "} " term:50 : term
macro_rules
| `($Γ ⊨.{$u} $p) => `(Entails.{$u} $Γ $p)

theorem Entails.axioms {p : Formula 𝓛} : p ∈ Axioms 𝓛 → Γ ⊨ p := by
  intros h 𝓜 ρ h₁
  clear h₁
  induction h generalizing ρ <;> simp [Formula.interp] <;> tauto
  case a4 p t =>
    intro h
    rw [Formula.interp_subst, Assignment.subst_single]
    apply h
  case a5 =>
    intros h u
    simp [Formula.shift, Formula.interp_subst, Assignment.subst_shift]
    exact h

theorem Entails.mp : Γ ⊨.{u} p ⟶ q → Γ ⊨.{u} p → Γ ⊨.{u} q := by
  intros h₁ h₂ 𝓜 ρ h
  apply h₁ 𝓜 ρ h
  exact h₂ 𝓜 ρ h

theorem soundness : Γ ⊢ p → Γ ⊨ p := by
  intro h
  induction h with
  | assumption h =>
      intros _ _ h₁
      apply h₁
      exact h
  | axioms h => exact Entails.axioms h
  | mp _ _ ih₁ ih₂ => exact Entails.mp ih₁ ih₂



def Satisfiable (Γ : Formulas 𝓛)
  := ∃ (𝓜 : Model.{u} 𝓛) (ρ : Assignment 𝓜), ∀ p ∈ Γ, ⟦ p ⟧ₚ 𝓜, ρ

theorem Satisfiable.weaken : Γ ⊆ Δ → Satisfiable.{u} Δ → Satisfiable.{u} Γ := by
  rintro h₁ ⟨𝓜, ⟨ρ, h₂⟩⟩
  exists 𝓜, ρ
  intros p h₃
  apply h₂
  apply h₁
  exact h₃
