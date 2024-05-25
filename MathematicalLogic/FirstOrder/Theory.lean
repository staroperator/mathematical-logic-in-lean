import MathematicalLogic.FirstOrder.Semantics

namespace FirstOrder.Language

@[reducible] def Theory (𝓛 : Language) := Set 𝓛.Sentence

namespace Theory

universe u v

def ctx (𝓣 : 𝓛.Theory) : Context 𝓛 := { BFormula.val p | p ∈ 𝓣 }

variable {𝓛 : Language} {𝓣 : 𝓛.Theory}

instance : Coe 𝓛.Theory 𝓛.Context := ⟨Theory.ctx⟩

theorem ax : p ∈ 𝓣 → 𝓣 ⊢ p.val := (Proof.hyp ⟨p, ·, rfl⟩)

lemma shift_eq : ↑ᶜ𝓣.ctx = 𝓣.ctx := by
  simp [ctx, Context.lift, Sentence.shift_eq]

theorem generalization_iff {p : 𝓛.Formula} :
  𝓣 ⊢ p ↔ 𝓣 ⊢ ∀' p := by
  nth_rw 1 [←Theory.shift_eq]
  apply Proof.generalization_iff

theorem generalization {p : 𝓛.Formula} :
  𝓣 ⊢ p → 𝓣 ⊢ ∀' p := generalization_iff.mp

theorem alls_iff {p : 𝓛.BFormula m} :
  𝓣 ⊢ p.val ↔ 𝓣 ⊢ (∀* p).val := by
  induction m with simp [BFormula.alls]
  | succ m ih => rw [generalization_iff]; apply @ih (∀ᵇ p)

abbrev Consistent (𝓣 : 𝓛.Theory) := 𝓣.ctx.Consistent

def Complete (𝓣 : 𝓛.Theory) :=
  ∀ (p : 𝓛.Sentence), 𝓣 ⊢ p.val ∨ 𝓣 ⊢ ~ p.val

def Decidable (𝓣 : 𝓛.Theory) :=
  ∀ (p : 𝓛.Formula), _root_.Decidable (𝓣 ⊢ p)



structure Model (𝓣 : 𝓛.Theory) extends Structure.{u} 𝓛 where
  satisfy𝓣 : ∀ p ∈ 𝓣, toStructure ⊨ₛ p

instance {𝓣 : 𝓛.Theory} : CoeOut 𝓣.Model 𝓛.Structure := ⟨Model.toStructure⟩

theorem soundness {p : 𝓛.Formula} {𝓜 : 𝓣.Model} {ρ : 𝓜.Assignment} :
  𝓣 ⊢ p → 𝓜 ⊨[ρ] p := by
  intro h
  apply Language.soundness
  · exact h
  · intro q ⟨p, h₁, h₂⟩; subst h₂
    simp [←Sentence.val_interp_eq]
    exact 𝓜.satisfy𝓣 p h₁

theorem soundness' {p : 𝓛.Sentence} {𝓜 : 𝓣.Model} :
  𝓣 ⊢ p.val → 𝓜 ⊨ₛ p := by
  intro h
  rw [Sentence.val_interp_eq (ρ := default)]
  apply soundness
  exact h

def Satisfiable (𝓣 : 𝓛.Theory) := Nonempty (Model.{u} 𝓣)

theorem Consistent.of_satisfiable : 𝓣.Satisfiable → 𝓣.Consistent := by
  intro ⟨𝓜⟩ h
  apply soundness' (𝓜 := 𝓜) (p := ⊥) at h
  exact h

end FirstOrder.Language.Theory
