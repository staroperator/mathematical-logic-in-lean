import MathematicalLogic.FirstOrder.Semantics
import MathematicalLogic.FirstOrder.Bounded

@[reducible] def Theory (𝓛) := Set (Sentence 𝓛)

def Theory.ctx (𝓣 : Theory 𝓛) : Context 𝓛 :=
  { BFormula.ub p | p ∈ 𝓣 }

def Theory.Proof (𝓣 : Theory 𝓛) (p : Formula 𝓛) := 𝓣.ctx ⊢ p

infix:50 " ⊢ᵀ " => Theory.Proof

theorem Theory.axioms {p : Sentence 𝓛} {𝓣 : Theory 𝓛} :
  p ∈ 𝓣 → 𝓣 ⊢ᵀ p.ub := by
  intro h
  apply Proof.assumption
  exists p

lemma Theory.shift_eq {𝓣 : Theory 𝓛} : ↑ₚₛ𝓣.ctx = 𝓣.ctx := by
  simp [ctx, Context.lift, Sentence.shift_eq]

theorem Theory.generalization {𝓣 : Theory 𝓛} {p : Formula 𝓛} :
  𝓣 ⊢ᵀ p → 𝓣 ⊢ᵀ ∀' p := by
  intro h
  apply Proof.generalization
  rw [Theory.shift_eq]
  exact h

def Model (𝓣 : Theory 𝓛) : Type (u + 1) :=
  { 𝓜 : Structure 𝓛 | ∀ p ∈ 𝓣, ⟦ p ⟧ₛᵇ 𝓜 }

namespace Model

variable {𝓣 : Theory 𝓛} (𝓜 : Model 𝓣)

@[reducible] def 𝓤 := 𝓜.val.𝓤
@[reducible] def 𝓕 {n} := 𝓜.val.𝓕 (n := n)
@[reducible] def 𝓟 {n} := 𝓜.val.𝓟 (n := n)

instance : CoeOut (Model 𝓣) (Structure 𝓛) where
  coe := Subtype.val

end Model

theorem Theory.soundness {𝓣 : Theory 𝓛} {p : Formula 𝓛} {𝓜 : Model 𝓣} {ρ : Assignment 𝓜} :
  𝓣 ⊢ᵀ p → ⟦ p ⟧ₚ 𝓜, ρ := by
  intro h
  apply _root_.soundness
  · exact h
  · intro q ⟨p, h₁, h₂⟩
    subst h₂
    simp [←Sentence.ub_interp_eq]
    apply 𝓜.property
    exact h₁
