import Mathlib.Data.Set.Finite
import MathematicalLogic.FirstOrder.Syntax

@[reducible] def Context (𝓛) := Set (Formula 𝓛)

def Context.add (Γ : Context 𝓛) (p) := insert p Γ
infixl:51 ",' " => Context.add

def Context.lift : Context 𝓛 → Context 𝓛 := λ Γ => {↑ₚp | p ∈ Γ}
prefix:max "↑ₚₛ" => Context.lift

inductive Axioms (𝓛) : Context 𝓛 where
| a1 : Axioms 𝓛 (p ⟶ (q ⟶ p))
| a2 : Axioms 𝓛 ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
| a3 : Axioms 𝓛 ((~ p ⟶ ~ q) ⟶ q ⟶ p)
| a4 : Axioms 𝓛 (∀' p ⟶ p[↦ₛ t]ₚ)
| a5 : Axioms 𝓛 (p ⟶ ∀' ↑ₚp)
| a6 : Axioms 𝓛 (∀' (p ⟶ q) ⟶ ∀' p ⟶ ∀' q)
| a7 : Axioms 𝓛 p → Axioms 𝓛 (∀' p)

inductive Proof (Γ : Context 𝓛) : Formula 𝓛 → Prop where
| assumption : p ∈ Γ → Proof Γ p
| axioms : p ∈ Axioms 𝓛 → Proof Γ p
| mp : Proof Γ (p ⟶ q) → Proof Γ p → Proof Γ q

infix:50 " ⊢ " => Proof

namespace Proof

theorem mp2 : Γ ⊢ p ⟶ q ⟶ r → Γ ⊢ p → Γ ⊢ q → Γ ⊢ r :=
  λ h₁ h₂ h₃ => mp (mp h₁ h₂) h₃

theorem weaken : Γ ⊆ Δ → Γ ⊢ p → Δ ⊢ p := by
  intros h₁ h₂
  induction h₂ with
  | assumption h => exact assumption (h₁ h)
  | axioms h => exact axioms h
  | mp _ _ ih₁ ih₂ => exact mp ih₁ ih₂

theorem weaken_add : Γ ⊢ p → Γ,' q ⊢ p := by
  apply weaken
  apply Set.subset_insert

theorem identity : Γ ⊢ p ⟶ p :=
  mp2 (axioms Axioms.a2) (axioms Axioms.a1) (axioms (Axioms.a1 (q := p)))

theorem deduction : Γ ⊢ p ⟶ q ↔ Γ,' p ⊢ q := by
  constructor
  · intro h
    apply mp
    · apply weaken
      · apply Set.subset_union_right
      · exact h
    · apply assumption
      left
      rfl
  · intro h
    induction h with
    | assumption h =>
      simp at h
      cases h with
      | inl h => cases h; apply identity
      | inr h => exact mp (axioms Axioms.a1) (assumption h)
    | axioms h => exact mp (axioms Axioms.a1) (axioms h)
    | mp _ _ ih₁ ih₂ => exact mp (mp (axioms Axioms.a2) ih₁) ih₂

macro "repeatn" n:num t:tactic : tactic => do
  let mut t' ← `(tactic| skip)
  for _ in [:n.getNat] do
    t' ← `(tactic| ($t'; $t))
  return t'

macro "passumption" : tactic =>
  `(tactic| (
    apply assumption
    repeat first | exact Or.inl rfl | apply Or.inr
  ))

macro "passumption" n:num : tactic =>
  `(tactic| (
    apply assumption
    repeatn $n apply Or.inr
    exact Or.inl rfl
  ))

macro "pweaken_ctx" : tactic => `(tactic| (intro _ h; (repeat apply Set.subset_insert); exact h))

macro "papply" t:term : tactic =>
  `(tactic| (
    first
    | apply mp $t
    | apply mp2 $t
    | apply λ h₁ h₂ h₃ => mp (mp (mp $t h₁) h₂) h₃
    | apply λ h₁ h₂ h₃ h₄ => mp (mp (mp (mp $t h₁) h₂) h₃) h₄
  ))

macro "papplyw" t:term : tactic =>
  `(tactic| (
    first
    | apply mp (weaken (by pweaken_ctx) $t)
    | apply mp2 (weaken (by pweaken_ctx) $t)
    | apply λ h₁ h₂ h₃ => mp (mp (mp (weaken (by pweaken_ctx) $t) h₁) h₂) h₃
    | apply λ h₁ h₂ h₃ h₄ => mp (mp (mp (mp (weaken (by pweaken_ctx) $t) h₁) h₂) h₃) h₄
  ))

macro "papply_assumption" n:num : tactic =>
  `(tactic| papply (by passumption $n))

macro "papply" n:num : tactic =>
  `(tactic| (
    first
    | apply mp; passumption $n
    | apply mp2; passumption $n
    | apply λ h h₁ h₂ h₃ => mp (mp (mp h h₁) h₂) h₃; passumption $n
    | apply λ h h₁ h₂ h₃ h₄ => mp (mp (mp (mp h h₁) h₂) h₃) h₄; passumption $n
  ))

macro "pintro" : tactic => `(tactic| apply deduction.mpr)
macro "pintros" : tactic => `(tactic| repeat pintro)
macro "pintros" n:num : tactic => `(tactic| repeatn $n pintro)

theorem composition : Γ ⊢ (p ⟶ q) ⟶ (q ⟶ r) ⟶ p ⟶ r := by
  pintros
  papply_assumption 1
  papply 2
  passumption

theorem contraposition : Γ ⊢ (p ⟶ q) ⟶ ~ q ⟶ ~ p := composition
theorem contraposition2 : Γ ⊢ (p ⟶ ~ q) ⟶ q ⟶ ~ p := by
  pintros
  papply 2 <;> passumption

theorem true_intro : Γ ⊢ ⊤ := identity

theorem false_elim : Γ ⊢ ⊥ ⟶ p := mp (axioms Axioms.a3) (mp (axioms Axioms.a1) true_intro)

theorem contradiction : Γ ⊢ ~ p ⟶ p ⟶ q := by
  pintros
  papply false_elim
  papply 1
  passumption

theorem double_neg1 : Γ ⊢ p ⟶ ~ ~ p := by
  pintros
  papply 0
  passumption

theorem double_neg2 : Γ ⊢ ~ ~ p ⟶ p := by
  pintro
  papply axioms Axioms.a3
  · pintros
    apply mp <;> passumption
  · passumption

theorem contraposition3 : Γ ⊢ (~ p ⟶ q) ⟶ ~ q ⟶ p := by
  papply composition
  · exact contraposition
  · papply (axioms Axioms.a2)
    pintro
    exact double_neg2

theorem not_imp_left : Γ ⊢ ~ (p ⟶ q) ⟶ p := by
  pintro
  papply double_neg2
  papply contraposition
  · exact contradiction (q := q)
  · passumption

theorem not_imp_right : Γ ⊢ ~ (p ⟶ q) ⟶ ~ q := by
  papply contraposition
  exact Proof.axioms Axioms.a1

theorem and_intro : Γ ⊢ p ⟶ q ⟶ p ⋀ q := by
  pintros
  apply mp2 <;> passumption

theorem and_left : Γ ⊢ p ⋀ q ⟶ p := by
  pintro
  papply double_neg2
  pintro
  papply 1
  pintros
  apply mp <;> passumption

theorem and_right : Γ ⊢ p ⋀ q ⟶ q := by
  pintro
  apply mp double_neg2
  pintro
  papply 1
  pintro
  passumption

theorem or_inl : Γ ⊢ p ⟶ p ⋁ q := by
  pintros
  papply false_elim
  apply mp <;> passumption

theorem or_inr : Γ ⊢ q ⟶ p ⋁ q := by
  pintros
  passumption

theorem or_elim : Γ ⊢ p ⋁ q ⟶ (p ⟶ r) ⟶ (q ⟶ r) ⟶ r := by
  pintros
  papply double_neg2
  pintro
  papply 0
  papply 2
  papply (axioms Axioms.a3)
  · apply mp2 composition
    · passumption
    · apply mp2 composition
      · passumption
      · apply double_neg1
  · passumption

theorem excluded_middle : Γ ⊢ ~ p ⋁ p := double_neg2

theorem iff_intro : Γ ⊢ (p ⟶ q) ⟶ (q ⟶ p) ⟶ (p ⟷ q) := and_intro
theorem iff_left : Γ ⊢ (p ⟷ q) ⟶ (p ⟶ q) := and_left
theorem iff_right : Γ ⊢ (p ⟷ q) ⟶ (q ⟶ p) := and_right

theorem iff_refl : Γ ⊢ p ⟷ p := mp2 iff_intro identity identity
theorem iff_symm : Γ ⊢ (p ⟷ q) ⟶ (q ⟷ p) := by
  pintro
  papply iff_intro
  · papply iff_right; passumption
  · papply iff_left; passumption
theorem iff_trans : Γ ⊢ (p ⟷ q) ⟶ (q ⟷ r) ⟶ (p ⟷ r) := by
  pintros 2
  papply iff_intro <;> apply mp2 composition
  · papply iff_left; passumption
  · papply iff_left; passumption
  · papply iff_right; passumption
  · papply iff_right; passumption
theorem iff_congr_imp : Γ ⊢ (p₁ ⟷ p₂) ⟶ (q₁ ⟷ q₂) ⟶ ((p₁ ⟶ q₁) ⟷ (p₂ ⟶ q₂)) := by
  pintros 2
  papply iff_intro <;> pintros
  · papply iff_left; passumption
    papply 1
    papply iff_right; passumption
    passumption
  · papply iff_right; passumption
    papply 1
    papply iff_left; passumption
    passumption

theorem generalization : ↑ₚₛΓ ⊢ p → Γ ⊢ ∀' p := by
  intro h
  induction h with
  | assumption h =>
    rcases h with ⟨p, ⟨h₁, h₂⟩⟩
    subst h₂
    exact mp (axioms Axioms.a5) (assumption h₁)
  | axioms h => exact axioms (Axioms.a7 h)
  | mp _ _ ih₁ ih₂ => exact mp2 (axioms Axioms.a6) ih₁ ih₂

theorem not_forall : Γ ⊢ ~ ∀' p ⟶ ∃' (~ p) := by
  papply contraposition
  papply (axioms Axioms.a6)
  apply generalization
  apply weaken
  · apply Set.empty_subset
  · apply double_neg2

theorem not_exists : Γ ⊢ ~ ∃' p ⟶ ∀' (~ p) := double_neg2

theorem forall_elim : Γ ⊢ ∀' p ⟶ p[↦ₛ t]ₚ := axioms Axioms.a4

theorem exists_intro : Γ ⊢ p[↦ₛ t]ₚ ⟶ ∃' p := by
  pintros
  suffices h : _ ⊢ (~ p)[↦ₛ t]ₚ by
    papply h
    passumption
  papply (axioms Axioms.a4)
  passumption

theorem exists_elim : Γ ⊢ ∃' p ⟶ (∀' (p ⟶ ↑ₚq)) ⟶ q := by
  pintros
  papply double_neg2
  pintros
  papply 2
  suffices h : _ ⊢ ∀' (↑ₚ(~ q) ⟶ ~ p) by
    apply mp2 (axioms Axioms.a6) h
    papply (axioms Axioms.a5)
    passumption
  papply (axioms Axioms.a6)
  · apply generalization
    exact contraposition
  · passumption

theorem exists_self : Γ ⊢ ∃' ↑ₚp ⟶ p := by
  papply contraposition3
  apply axioms Axioms.a5

theorem compactness : Γ ⊢ p → ∃ Δ, Δ ⊆ Γ ∧ Δ.Finite ∧ Δ ⊢ p := by
  intro h
  induction h with
  | @assumption p h =>
      exists {p}
      constructor
      · simp [h]
      constructor
      · simp
      · passumption; rfl
  | axioms h =>
      exists ∅
      constructor
      · simp
      constructor
      · simp
      · exact axioms h
  | mp _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨Δ₁, h₁, h₂, h₃⟩
      rcases ih₂ with ⟨Δ₂, h₄, h₅, h₆⟩
      exists Δ₁ ∪ Δ₂
      constructor
      · simp [h₁, h₄]
      constructor
      · simp [h₂, h₅]
      · apply Proof.mp
        · apply weaken
          · apply Set.subset_union_left
          · exact h₃
        · apply weaken
          · apply Set.subset_union_right
          · exact h₆

end Proof



notation Γ:50 "⊬" p:50 => ¬ Γ ⊢ p

def Consistent (Γ : Context 𝓛) := Γ ⊬ ⊥

theorem Consistent.weaken : Γ ⊆ Δ → Consistent Δ → Consistent Γ := by
  intros h₁ h₂ h
  apply h₂
  apply Proof.weaken
  · exact h₁
  · exact h

theorem Consistent.add : Consistent (Γ,' p) ↔ Γ ⊬ ~ p := by
  constructor
  · intro h₁ h₂
    apply h₁
    rw [←Proof.deduction]
    exact h₂
  · intro h₁ h₂
    apply h₁
    pintro
    exact h₂
