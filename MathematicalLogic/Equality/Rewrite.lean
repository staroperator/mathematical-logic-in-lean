import MathematicalLogic.Equality.Theory

variable [EqLanguage 𝓛] {𝓣 : Theory 𝓛} [EqTheory 𝓣]

mutual
inductive Term.Rewritable (t₁ t₂ : Term 𝓛) : Term 𝓛 → Term 𝓛 → Prop where
| matched : Term.Rewritable t₁ t₂ t₁ t₂
| refl : Term.Rewritable t₁ t₂ t t
| func {ts₁ ts₂ : Terms 𝓛 n} :
  Terms.Rewritable t₁ t₂ ts₁ ts₂ → Term.Rewritable t₁ t₂ (f ⬝ₜ ts₁) (f ⬝ₜ ts₂)
inductive Terms.Rewritable (t₁ t₂ : Term 𝓛) : Terms 𝓛 n → Terms 𝓛 n → Prop where
| nil : Terms.Rewritable t₁ t₂ []ₜ []ₜ
| cons :
  Term.Rewritable t₁ t₂ t₁' t₂' → Terms.Rewritable t₁ t₂ ts₁ ts₂ →
  Terms.Rewritable t₁ t₂ (t₁' ∷ₜ ts₁) (t₂' ∷ₜ ts₂)
end

inductive Formula.Rewritable (t₁ t₂ : Term 𝓛) : Formula 𝓛 → Formula 𝓛 → Prop where
| atom : Terms.Rewritable t₁ t₂ ts₁ ts₂ → Formula.Rewritable t₁ t₂ (p ⬝ₚ ts₁) (p ⬝ₚ ts₂)
| false : Formula.Rewritable t₁ t₂ ⊥ ⊥
| imp :
  Formula.Rewritable t₁ t₂ p₁ p₂ → Formula.Rewritable t₁ t₂ q₁ q₂ →
  Formula.Rewritable t₁ t₂ (p₁ ⟶ q₁) (p₂ ⟶ q₂)
| all : Formula.Rewritable t₁ t₂ (∀' p) (∀' p)

namespace Formula.Rewritable

def eq : Term.Rewritable t₁ t₂ t₁' t₂' → Term.Rewritable t₁ t₂ t₃' t₄' → Formula.Rewritable t₁ t₂ (t₁' ≈ t₃') (t₂' ≈ (t₄' : Term 𝓛)) :=
  λ h₁ h₂ => atom (Terms.Rewritable.cons h₁ (Terms.Rewritable.cons h₂ Terms.Rewritable.nil))

def not : Formula.Rewritable t₁ t₂ p₁ p₂ → Formula.Rewritable t₁ t₂ (~ p₁) (~ p₂) :=
  λ h => imp h false

def or : Formula.Rewritable t₁ t₂ p₁ p₂ → Formula.Rewritable t₁ t₂ q₁ q₂ → Formula.Rewritable t₁ t₂ (p₁ ⋁ q₁) (p₂ ⋁ q₂) :=
  λ h₁ h₂ => imp (not h₁) h₂

def and : Formula.Rewritable t₁ t₂ p₁ p₂ → Formula.Rewritable t₁ t₂ q₁ q₂ → Formula.Rewritable t₁ t₂ (p₁ ⋀ q₁) (p₂ ⋀ q₂) :=
  λ h₁ h₂ => not (imp h₁ (not h₂))

def iff : Formula.Rewritable t₁ t₂ p₁ p₂ → Formula.Rewritable t₁ t₂ q₁ q₂ → Formula.Rewritable t₁ t₂ (p₁ ⟷ q₁) (p₂ ⟷ q₂) :=
  λ h₁ h₂ => and (imp h₁ h₂) (imp h₂ h₁)

end Formula.Rewritable

mutual
theorem Term.Rewritable.soundness {Γ : Context 𝓛} {t₁' : Term 𝓛} :
  Γ ⊢ t₁ ≈ t₂ → 𝓣.toContext ⊆ Γ → Term.Rewritable t₁ t₂ t₁' t₂' →
  Γ ⊢ t₁' ≈ t₂' := λ h₁ h₂ h =>
  match h with
  | Term.Rewritable.matched => h₁
  | Term.Rewritable.refl => Proof.weaken h₂ Proof.refl
  | Term.Rewritable.func h => Proof.mp (Proof.weaken h₂ Proof.congr_func) (Terms.Rewritable.soundness h₁ h₂ h)
theorem Terms.Rewritable.soundness {Γ : Context 𝓛} {ts₁ : Terms 𝓛 n} :
  Γ ⊢ t₁ ≈ t₂ → 𝓣.toContext ⊆ Γ → Terms.Rewritable t₁ t₂ ts₁ ts₂ →
  Γ ⊢ ts₁ ≈ ts₂ := λ h₁ h₂ h =>
  match h with
  | Terms.Rewritable.nil => Proof.true_intro
  | Terms.Rewritable.cons h h' => Proof.mp2 Proof.and_intro (Term.Rewritable.soundness h₁ h₂ h) (Terms.Rewritable.soundness h₁ h₂ h')
end

theorem Formula.Rewritable.soundness {Γ : Context 𝓛} :
  𝓣.toContext ⊆ Γ → Γ ⊢ t₁ ≈ t₂ → Formula.Rewritable t₁ t₂ p₁ p₂ →
  Γ ⊢ p₁ ⟷ p₂ := by
  intros h₂ h₁ h
  induction h with
  | atom h => 
    apply Proof.mp
    · exact Proof.weaken h₂ Proof.congr_atom_iff
    · exact Terms.Rewritable.soundness h₁ h₂ h
  | false => exact Proof.iff_refl
  | imp _ _ ih₁ ih₂ =>
    apply Proof.mp2 Proof.iff_congr_imp <;> assumption
  | all => exact Proof.iff_refl

macro "prw" "by" t:tactic : tactic => `(tactic| (
  apply Proof.mp2 Proof.iff_right
  · apply Formula.Rewritable.soundness (by intros _ h; (repeat apply Set.subset_insert); exact h)
    · ($t; skip)
    · focus repeat first
      | apply Formula.Rewritable.all
      | apply Formula.Rewritable.iff
      | apply Formula.Rewritable.and
      | apply Formula.Rewritable.or
      | apply Formula.Rewritable.not
      | apply Formula.Rewritable.imp
      | apply Formula.Rewritable.eq
      | apply Formula.Rewritable.atom
      | apply Terms.Rewritable.nil
      | apply Terms.Rewritable.cons
      | apply Term.Rewritable.matched
      | apply Term.Rewritable.func
      | apply Term.Rewritable.refl
      | skip))

macro "prw" t:term : tactic => `(tactic| prw by exact $t)
macro "prw" n:num : tactic => `(tactic| prw by passumption at $n)
