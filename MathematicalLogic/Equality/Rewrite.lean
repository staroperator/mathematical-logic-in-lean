import MathematicalLogic.Equality.Theory

variable [EqLanguage 𝓛] {𝓣 : Theory 𝓛} [EqTheory 𝓣]

mutual
inductive Term.Rewritable (Γ : Context 𝓛) : Term 𝓛 → Term 𝓛 → Prop where
| matched : Γ ⊢ t₁ ≈ t₂ → Term.Rewritable Γ t₁ t₂
| func : Terms.Rewritable Γ ts₁ ts₂ → Term.Rewritable Γ (f ⬝ₜ ts₁) (f ⬝ₜ ts₂)
| refl : Term.Rewritable Γ t t
inductive Terms.Rewritable (Γ : Context 𝓛) : Terms 𝓛 n → Terms 𝓛 n → Prop where
| nil : Terms.Rewritable Γ []ₜ []ₜ
| cons : Term.Rewritable Γ t₁ t₂ → Terms.Rewritable Γ ts₁ ts₂ →
  Terms.Rewritable Γ (t₁ ∷ₜ ts₁) (t₂ ∷ₜ ts₂)
end

inductive Formula.Rewritable (Γ : Context 𝓛) : Formula 𝓛 → Formula 𝓛 → Prop where
| atom : Terms.Rewritable Γ ts₁ ts₂ → Formula.Rewritable Γ (p ⬝ₚ ts₁) (p ⬝ₚ ts₂)
| imp : Formula.Rewritable Γ p₁ p₂ → Formula.Rewritable Γ q₁ q₂ →
  Formula.Rewritable Γ (p₁ ⇒ q₁) (p₂ ⇒ q₂)
| refl : Formula.Rewritable Γ p p

mutual
theorem Term.Rewritable.soundness (h : 𝓣.ctx ⊆ Γ) : Term.Rewritable Γ t₁ t₂ → Γ ⊢ t₁ ≈ t₂
| Term.Rewritable.matched h₁ => h₁
| Term.Rewritable.refl => Proof.weaken h Proof.refl
| Term.Rewritable.func h₁ => Proof.mp (Proof.weaken h Proof.congr_func) (Terms.Rewritable.soundness h h₁)
theorem Terms.Rewritable.soundness (h : 𝓣.ctx ⊆ Γ) : Terms.Rewritable Γ ts₁ ts₂ → Γ ⊢ ts₁ ≋ ts₂
| Terms.Rewritable.nil => Proof.true_intro
| Terms.Rewritable.cons h₁ h₂ => Proof.mp2 Proof.and_intro (Term.Rewritable.soundness h h₁) (Terms.Rewritable.soundness h h₂)
end

theorem Formula.Rewritable.soundness (h : 𝓣.ctx ⊆ Γ) :
  Formula.Rewritable Γ p q → Γ ⊢ p ⇔ q
| Formula.Rewritable.atom h₁ => Proof.mp (Proof.weaken h Proof.congr_atom_iff) (Terms.Rewritable.soundness h h₁)
| Formula.Rewritable.imp h₁ h₂ => Proof.mp2 Proof.iff_congr_imp (Formula.Rewritable.soundness h h₁) (Formula.Rewritable.soundness h h₂)
| Formula.Rewritable.refl => Proof.iff_refl

macro "prw_by" t:tactic : tactic => `(tactic| (
  apply Proof.mp2 Proof.iff_right
  · apply Formula.Rewritable.soundness (by pweaken_ctx)
    focus repeat' (
      first
      | exact Term.Rewritable.matched (by ($t; skip))
      | eapply Formula.Rewritable.atom
      | eapply Formula.Rewritable.imp
      | exact Terms.Rewritable.nil
      | eapply Terms.Rewritable.cons
      | eapply Term.Rewritable.func
      | exact Formula.Rewritable.refl
      | exact Term.Rewritable.refl)
  simp))

syntax "prwa" "←"? num : tactic
macro_rules
| `(tactic| prwa $n) => `(tactic| prw_by passumption $n)
| `(tactic| prwa ←$n) => `(tactic| prw_by (psymm; passumption $n))

syntax "prw" "←"? term : tactic
macro_rules
| `(tactic| prw $t) =>
  `(tactic| prw_by (exact Proof.weaken (by pweaken_ctx) $t))
| `(tactic| prw ←$t) =>
  `(tactic| prw_by (psymm; exact Proof.weaken (by pweaken_ctx) $t))
