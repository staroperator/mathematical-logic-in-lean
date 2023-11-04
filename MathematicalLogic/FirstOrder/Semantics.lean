import Mathlib.Data.Vector
import MathematicalLogic.FirstOrder.Proof

universe u v

structure Structure (𝓛 : Language) where
  𝓤 : Type u
  inhabited : Inhabited 𝓤
  𝓕 : 𝓛.𝓕 n → Vector 𝓤 n → 𝓤
  𝓟 : 𝓛.𝓟 n → Vector 𝓤 n → Prop

instance {𝓜 : Structure 𝓛} : Inhabited 𝓜.𝓤 := 𝓜.inhabited

def Assignment (𝓜: Structure 𝓛) := ℕ → 𝓜.𝓤

instance : Inhabited (Assignment 𝓜) := ⟨λ _ => default⟩

def Assignment.cons (u : 𝓜.𝓤) (ρ : Assignment 𝓜) : Assignment 𝓜
| 0 => u
| x + 1 => ρ x

infixr:80 " ∷ₐ " => Assignment.cons

mutual
@[simp] def Term.interp : Term 𝓛 → (𝓜 : Structure 𝓛) → Assignment 𝓜 → 𝓜.𝓤
| #x, _, ρ => ρ x
| f ⬝ₜ ts, 𝓜, ρ => 𝓜.𝓕 f (ts.interp 𝓜 ρ)
@[simp] def Terms.interp : Terms 𝓛 n → (𝓜 : Structure 𝓛) → Assignment 𝓜 → Vector 𝓜.𝓤 n
| []ₜ, _, _ => []ᵥ
| t ∷ₜ ts, 𝓜, ρ => t.interp 𝓜 ρ ∷ᵥ ts.interp 𝓜 ρ
end

notation:80 "⟦" t "⟧ₜ " 𝓜 ", " ρ:80 => Term.interp t 𝓜 ρ
notation:80 "⟦" ts "⟧ₜₛ " 𝓜 ", " ρ:80 => Terms.interp ts 𝓜 ρ

theorem Terms.interp_of_vector {v : Vector (Term 𝓛) n} :
  ⟦ v ⟧ₜₛ 𝓜, ρ = Vector.ofFn (λ x => ⟦ v.get x ⟧ₜ 𝓜, ρ) := by
  induction v using Vector.inductionOn
  · rfl
  · simp; congr

def Assignment.subst {𝓜 : Structure 𝓛} (ρ : Assignment 𝓜) (σ : Subst 𝓛) : Assignment 𝓜 :=
  λ x => ⟦ σ x ⟧ₜ 𝓜, ρ

notation:80 ρ "[" σ "]ₐ" => Assignment.subst ρ σ

lemma Assignment.subst_shift {ρ : Assignment 𝓜} : (u ∷ₐ ρ)[Subst.shift]ₐ = ρ := by
  funext x
  simp [Assignment.subst, Subst.shift, Assignment.cons]

lemma Assignment.subst_single {ρ : Assignment 𝓜} : ρ[↦ₛ t]ₐ = (⟦ t ⟧ₜ 𝓜, ρ) ∷ₐ ρ := by
  funext x
  cases x with
  | zero => rfl
  | succ => simp [Assignment.subst, Subst.single, Assignment.cons]

mutual
theorem Term.interp_subst : ⟦ t[σ]ₜ ⟧ₜ 𝓜, ρ = ⟦ t ⟧ₜ 𝓜, ρ[σ]ₐ := match t with
| #x => by simp [Assignment.subst]
| f ⬝ₜ ts => by simp; rw [Terms.interp_subst]
theorem Terms.interp_subst : ⟦ ts[σ]ₜₛ ⟧ₜₛ 𝓜, ρ = ⟦ ts ⟧ₜₛ 𝓜, ρ[σ]ₐ := match ts with
| []ₜ => by rfl
| t ∷ₜ ts => by simp; rw [Term.interp_subst, Terms.interp_subst]
end



@[simp] def Formula.interp : Formula 𝓛 → (𝓜 : Structure 𝓛) → Assignment 𝓜 → Prop
| p ⬝ₚ ts, 𝓜, ρ => 𝓜.𝓟 p (⟦ ts ⟧ₜₛ 𝓜, ρ)
| ⊥, _, _ => False
| p ⟶ q, 𝓜, ρ => p.interp 𝓜 ρ → q.interp 𝓜 ρ
| ∀' p, 𝓜, ρ => ∀ u, p.interp 𝓜 (u ∷ₐ ρ)

notation:80 "⟦" p "⟧ₚ " 𝓜 ", " ρ:80 => Formula.interp p 𝓜 ρ

theorem Formula.interp_subst : ⟦ p[σ]ₚ ⟧ₚ 𝓜, ρ ↔ ⟦ p ⟧ₚ 𝓜, ρ[σ]ₐ := by
  induction p generalizing ρ σ with
  | atom => simp [Terms.interp_subst]
  | false => rfl
  | imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | all _ ih =>
      rw [Formula.interp]
      apply forall_congr'
      intro u
      rw [ih]
      congr!
      funext x
      cases x
      · rfl
      · simp [Assignment.subst, Subst.lift, Term.shift]
        conv => lhs; simp [Term.interp_subst, Assignment.subst_shift]

theorem Formula.interp_imp :
  ⟦ p ⟶ q ⟧ₚ 𝓜, ρ ↔ ⟦ p ⟧ₚ 𝓜, ρ → ⟦ q ⟧ₚ 𝓜, ρ := by simp

theorem Formula.interp_neg :
  ⟦ ~ p ⟧ₚ 𝓜, ρ ↔ ¬ ⟦ p ⟧ₚ 𝓜, ρ := by simp

theorem Formula.interp_and :
  ⟦ p ⋀ q ⟧ₚ 𝓜, ρ ↔ (⟦ p ⟧ₚ 𝓜, ρ ∧ ⟦ q ⟧ₚ 𝓜, ρ) := by simp; tauto

theorem Formula.interp_or :
  ⟦ p ⋁ q ⟧ₚ 𝓜, ρ ↔ (⟦ p ⟧ₚ 𝓜, ρ ∨ ⟦ q ⟧ₚ 𝓜, ρ) := by simp; tauto

theorem Formula.interp_iff :
  ⟦ p ⟷ q ⟧ₚ 𝓜, ρ ↔ (⟦ p ⟧ₚ 𝓜, ρ ↔ ⟦ q ⟧ₚ 𝓜, ρ) := by simp; tauto

theorem Formula.interp_exists :
  ⟦ ∃' p ⟧ₚ 𝓜, ρ ↔ ∃ u, ⟦ p ⟧ₚ 𝓜, u ∷ₐ ρ := by simp [imp_false]



def Entails (Γ : Context 𝓛) (p) :=
  ∀ (𝓜 : Structure.{u} 𝓛) (ρ : Assignment 𝓜),
    (∀ q ∈ Γ, ⟦ q ⟧ₚ 𝓜, ρ) → ⟦ p ⟧ₚ 𝓜, ρ

infix:50 " ⊨ " => Entails
syntax:50 term " ⊨.{" level "} " term:50 : term
macro_rules
| `($Γ ⊨.{$u} $p) => `(Entails.{$u} $Γ $p)

theorem Entails.axioms {p : Formula 𝓛} : p ∈ Axioms 𝓛 → Γ ⊨ p := by
  intros h 𝓜 ρ h₁
  clear h₁
  induction h generalizing ρ <;> simp <;> tauto
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



def Satisfiable (Γ : Context 𝓛) :=
  ∃ (𝓜 : Structure.{u} 𝓛) (ρ : Assignment 𝓜), ∀ p ∈ Γ, ⟦ p ⟧ₚ 𝓜, ρ

theorem Satisfiable.weaken : Γ ⊆ Δ → Satisfiable.{u} Δ → Satisfiable.{u} Γ := by
  rintro h₁ ⟨𝓜, ⟨ρ, h₂⟩⟩
  exists 𝓜, ρ
  intros p h₃
  apply h₂
  apply h₁
  exact h₃



def Structure.ulift (𝓜 : Structure.{u} 𝓛) : Structure.{max u v} 𝓛 where
  𝓤 := ULift.{v} 𝓜.𝓤
  inhabited := ⟨ULift.up default⟩
  𝓕 := λ f v => ULift.up (𝓜.𝓕 f (v.map ULift.down))
  𝓟 := λ p v => 𝓜.𝓟 p (v.map ULift.down)

def Assignment.ulift (ρ : Assignment 𝓜) : Assignment (𝓜.ulift) :=
  λ x => ULift.up (ρ x)

lemma Assignment.ulift_cons {𝓜 : Structure.{u} 𝓛} {ρ : Assignment.{u} 𝓜} {u : 𝓜.𝓤} : (u ∷ₐ ρ).ulift = Assignment.cons (𝓜 := 𝓜.ulift) (ULift.up u) ρ.ulift := by
  funext x; cases x <;> rfl

lemma Vector.map_comp {v : Vector α n} : (v.map f).map g = v.map (g ∘ f) := by
  induction n with
  | zero => simp
  | succ n ih => rw [←Vector.cons_head_tail (v := v)]; simp only [Vector.map_cons, Function.comp, ih]

lemma ULift.down_comp_up : ULift.down ∘ ULift.up = id (α := α) := by
  funext x; simp

mutual
lemma Term.interp_ulift {𝓜 : Structure 𝓛} {ρ : Assignment 𝓜} :
  ⟦ t ⟧ₜ 𝓜.ulift, ρ.ulift = ULift.up (⟦ t ⟧ₜ 𝓜, ρ) :=
  match t with
  | #x => by simp [Assignment.ulift]
  | f ⬝ₜ ts => by
    simp
    rw [Terms.interp_ulift]
    unfold Structure.ulift
    simp [Vector.map_comp, ULift.down_comp_up]
lemma Terms.interp_ulift {𝓜 : Structure 𝓛} {ρ : Assignment 𝓜} :
  ⟦ ts ⟧ₜₛ 𝓜.ulift, ρ.ulift = (⟦ ts ⟧ₜₛ 𝓜, ρ).map ULift.up :=
  match ts with
  | []ₜ => rfl
  | t ∷ₜ ts => by
    simp
    rw [Term.interp_ulift, Terms.interp_ulift]
end

lemma Formula.interp_ulift {𝓜 : Structure 𝓛} {ρ : Assignment 𝓜} :
  ⟦ p ⟧ₚ 𝓜.ulift, ρ.ulift ↔ ⟦ p ⟧ₚ 𝓜, ρ := by
  induction p generalizing ρ <;> simp [Formula.interp]
  case atom p ts =>
    simp [Terms.interp_ulift]
    unfold Structure.ulift
    simp [Vector.map_comp, ULift.down_comp_up]
  case imp p q ih₁ ih₂ =>
    simp [ih₁, ih₂]
  case all p ih =>
    constructor
    · intros h u
      rw [←ih, Assignment.ulift_cons]
      apply h
    · intros h u
      rw [←ULift.up_down u, ←Assignment.ulift_cons, ih]
      apply h

theorem Entails.down : Γ ⊨.{max u v} p → Γ ⊨.{u} p := by
  intros h 𝓜 ρ h₁
  have h₂ := h (Structure.ulift.{u, v} 𝓜) ρ.ulift
  simp [Formula.interp_ulift] at h₂
  exact h₂ h₁

theorem Satisfiable.up : Satisfiable.{u} Γ → Satisfiable.{max u v} Γ := by
  intro h
  rcases h with ⟨𝓜, ρ, h⟩
  exists (Structure.ulift.{u, v} 𝓜), ρ.ulift
  simp [Formula.interp_ulift]
  exact h
