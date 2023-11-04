import MathematicalLogic.FirstOrder.Semantics
import MathematicalLogic.FirstOrder.Bounded

universe u

@[reducible] def Theory (𝓛) := Set (Sentence 𝓛)

def Theory.toContext (𝓣 : Theory 𝓛) : Context 𝓛 := {↑p | p ∈ 𝓣}

def Theory.Proof (𝓣 : Theory 𝓛) (p : Formula 𝓛) := 𝓣.toContext ⊢ p

infix:50 " ⊢ " => Theory.Proof

theorem Theory.axioms {p : Sentence 𝓛} {𝓣 : Theory 𝓛} :
  p ∈ 𝓣 → 𝓣 ⊢ ↑p := by
  intro h
  apply Proof.assumption
  exists p

lemma Theory.shift_eq {𝓣 : Theory 𝓛} : ↑ₚₛ𝓣.toContext = 𝓣.toContext := by
  unfold Theory.toContext
  simp [Context.lift, Sentence.shift_eq]

theorem Theory.generalization {𝓣 : Theory 𝓛} :
  𝓣 ⊢ p → 𝓣 ⊢ ∀' p := by
  intro h
  apply Proof.generalization
  rw [Theory.shift_eq]
  exact h

def Theory.Model (𝓣 : Theory 𝓛) : Type (u + 1) :=
  { 𝓜 : _root_.Model 𝓛 | ∀ p ∈ 𝓣, ⟦ p ⟧ₛ 𝓜 }

namespace Theory.Model

variable {𝓣 : Theory 𝓛} (𝓜 : 𝓣.Model)

@[reducible] def 𝓤 := 𝓜.val.𝓤
@[reducible] def 𝓕 {n} := 𝓜.val.𝓕 (n := n)
@[reducible] def 𝓟 {n} := 𝓜.val.𝓟 (n := n)

end Theory.Model

instance {𝓣 : Theory 𝓛} : CoeOut (𝓣.Model) (Model 𝓛) where
  coe := Subtype.val

theorem Theory.soundness
  {𝓣 : Theory 𝓛} {𝓜 : 𝓣.Model} {ρ : Assignment 𝓜} :
  𝓣 ⊢ p → ⟦ p ⟧ₚ 𝓜, ρ := by
  rintro h
  apply _root_.soundness
  · exact h
  · rintro q ⟨p, h₁, h₂⟩
    subst h₂
    simp [←Sentence.unbounded_interp_eq]
    apply 𝓜.property
    exact h₁
