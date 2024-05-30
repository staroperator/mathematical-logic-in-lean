import MathematicalLogic.FirstOrder.Proof

universe u v

namespace FirstOrder.Language

structure Structure (𝓛 : Language) where
  𝓤 : Type u
  inhabited𝓤 : Inhabited 𝓤
  interp𝓕 : 𝓛.𝓕 n → Vec 𝓤 n → 𝓤
  interp𝓡 : 𝓛.𝓡 n → Vec 𝓤 n → Prop

variable {𝓛 : Language} {𝓢 : 𝓛.Structure}

namespace Structure

instance : Inhabited 𝓢.𝓤 := 𝓢.inhabited𝓤

def Assignment (𝓢: 𝓛.Structure) := ℕ → 𝓢.𝓤

instance : Inhabited (𝓢.Assignment) := ⟨λ _ => default⟩

def Assignment.cons (u : 𝓢.𝓤) (ρ : 𝓢.Assignment) : 𝓢.Assignment
| 0 => u
| x + 1 => ρ x
infixr:80 " ∷ₐ " => Assignment.cons

end Structure

open Structure

def Term.interp : 𝓛.Term → (𝓢 : 𝓛.Structure) → 𝓢.Assignment → 𝓢.𝓤
| #x, _, ρ => ρ x
| f ⬝ₜ v, 𝓢, ρ => 𝓢.interp𝓕 f (λ i => (v i).interp 𝓢 ρ)
notation:80 "⟦" t "⟧ₜ " 𝓢 ", " ρ:80 => Term.interp t 𝓢 ρ

namespace Structure

def Assignment.subst (ρ : 𝓢.Assignment) (σ : 𝓛.Subst) : 𝓢.Assignment :=
  λ x => ⟦ σ x ⟧ₜ 𝓢, ρ
notation:80 ρ "[" σ "]ₐ" => Structure.Assignment.subst ρ σ

variable {ρ : 𝓢.Assignment}

lemma Assignment.subst_shift : (u ∷ₐ ρ)[Subst.shift]ₐ = ρ := by
  funext x
  simp [Assignment.subst, Assignment.cons, Term.interp]

lemma Assignment.subst_single : ρ[↦ₛ t]ₐ = (⟦ t ⟧ₜ 𝓢, ρ) ∷ₐ ρ := by
  funext x
  cases x with
  | zero => rfl
  | succ => simp [Assignment.subst, Assignment.cons, Term.interp]

end Structure

theorem Term.interp_subst : ⟦ t[σ]ₜ ⟧ₜ 𝓢, ρ = ⟦ t ⟧ₜ 𝓢, ρ[σ]ₐ := by
  induction t with simp [Structure.Assignment.subst, interp]
  | func f v ih => funext; simp [ih]



def Formula.interp : 𝓛.Formula → (𝓢 : 𝓛.Structure) → 𝓢.Assignment → Prop
| r ⬝ᵣ v, 𝓢, ρ => 𝓢.interp𝓡 r (λ i => ⟦ v i ⟧ₜ 𝓢, ρ)
| t₁ ≐ t₂, 𝓢, ρ => ⟦ t₁ ⟧ₜ 𝓢, ρ = ⟦ t₂ ⟧ₜ 𝓢, ρ
| ⊥, _, _ => False
| p ⇒ q, 𝓢, ρ => p.interp 𝓢 ρ → q.interp 𝓢 ρ
| ∀' p, 𝓢, ρ => ∀ u, p.interp 𝓢 (u ∷ₐ ρ)
notation:50 𝓢 " ⊨[" ρ "] " p:50 => Formula.interp p 𝓢 ρ

theorem Formula.interp_subst : 𝓢 ⊨[ρ] p[σ]ₚ ↔ 𝓢 ⊨[ρ[σ]ₐ] p := by
  induction p generalizing ρ σ with simp [Assignment.subst, interp]
  | rel => simp [Term.interp_subst]
  | eq t₁ t₂ => simp [Term.interp_subst]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih =>
      apply forall_congr'
      intro u; simp [ih]; congr!
      funext x; cases x
      · rfl
      · simp [Assignment.cons, Assignment.subst, Term.interp, Term.shift, Term.interp_subst]
        rfl

theorem Formula.interp_neg :
  𝓢 ⊨[ρ] ~ p ↔ ¬ 𝓢 ⊨[ρ] p := by simp [interp]

theorem Formula.interp_or :
  𝓢 ⊨[ρ] p ⩒ q ↔ 𝓢 ⊨[ρ] p ∨ 𝓢 ⊨[ρ] q := by simp [interp]; tauto

theorem Formula.interp_and :
  𝓢 ⊨[ρ] p ⩑ q ↔ 𝓢 ⊨[ρ] p ∧ 𝓢 ⊨[ρ] q := by simp [interp]

theorem Formula.interp_iff :
  𝓢 ⊨[ρ] p ⇔ q ↔ (𝓢 ⊨[ρ] p ↔ 𝓢 ⊨[ρ] q) := by simp [interp]; tauto

theorem Formula.interp_exists :
  𝓢 ⊨[ρ] ∃' p ↔ ∃ u, 𝓢 ⊨[u ∷ₐ ρ] p := by simp [interp]



def Entails (Γ : 𝓛.Context) (p) :=
  ∀ (𝓢 : Structure.{u} 𝓛) (ρ), (∀ q ∈ Γ, 𝓢 ⊨[ρ] q) → 𝓢 ⊨[ρ] p

infix:50 " ⊨ " => Entails
syntax:50 term " ⊨.{" level "} " term:50 : term
macro_rules
| `($Γ ⊨.{$u} $p) => `(Entails.{$u} $Γ $p)

theorem Entails.axioms {p : Formula 𝓛} : p ∈ Axioms 𝓛 → Γ ⊨ p := by
  intros h 𝓢 ρ h₁
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
  case e2 =>
    intros h
    simp [Formula.interp_subst, Assignment.subst_single, h]

theorem Entails.mp : Γ ⊨.{u} p ⇒ q → Γ ⊨.{u} p → Γ ⊨.{u} q := by
  intros h₁ h₂ 𝓢 ρ h
  apply h₁ 𝓢 ρ h
  exact h₂ 𝓢 ρ h

theorem soundness : Γ ⊢ p → Γ ⊨ p := by
  intro h
  induction h with
  | hyp h => intros _ _ h₁; apply h₁; exact h
  | ax h => exact Entails.axioms h
  | mp _ _ ih₁ ih₂ => exact Entails.mp ih₁ ih₂



def Structure.BAssignment (𝓢 : 𝓛.Structure) (n : ℕ) := Vec 𝓢.𝓤 n

def BTerm.interp : 𝓛.BTerm m → (𝓢 : 𝓛.Structure) → 𝓢.BAssignment m → 𝓢.𝓤
| #ᵇx, _, ρ => ρ x
| f ⬝ₜᵇ v, 𝓢, ρ => 𝓢.interp𝓕 f (λ i => (v i).interp 𝓢 ρ)
notation:80 "⟦" t "⟧ᵇ " 𝓢 ", " ρ:80 => BTerm.interp t 𝓢 ρ

theorem BTerm.val_interp_eq {ρ : 𝓢.BAssignment m} :
  (∀ x, ρ x = ρ' x) → ⟦ t ⟧ᵇ 𝓢, ρ = ⟦ t.val ⟧ₜ 𝓢, ρ' := by
  intro h
  induction t with simp [interp, Term.interp]
  | var x => apply h
  | func f v ih => funext; simp [ih _ h]

def BFormula.interp : 𝓛.BFormula m → (𝓢 : 𝓛.Structure) → 𝓢.BAssignment m → Prop
| r ⬝ᵣᵇ v, 𝓢, ρ => 𝓢.interp𝓡 r (λ i => ⟦ v i ⟧ᵇ 𝓢, ρ)
| t₁ ≐ᵇ t₂, 𝓢, ρ => ⟦ t₁ ⟧ᵇ 𝓢, ρ = ⟦ t₂ ⟧ᵇ 𝓢, ρ
| ⊥, _, _ => False
| p ⇒ q, 𝓜, ρ => p.interp 𝓜 ρ → q.interp 𝓜 ρ
| ∀ᵇ p, 𝓜, ρ => ∀ u, p.interp 𝓜 (u ∷ᵥ ρ)
notation:50 𝓢 " ⊨[" ρ "]ᵇ " p:50 => BFormula.interp p 𝓢 ρ

def Sentence.interp (p : 𝓛.Sentence) (𝓢 : 𝓛.Structure) :=
  𝓢 ⊨[[]ᵥ]ᵇ p
notation:50 𝓢 " ⊨ₛ " p:50 => Sentence.interp p 𝓢

theorem BFormula.interp_neg :
  𝓢 ⊨[ρ]ᵇ ~ p ↔ ¬ 𝓢 ⊨[ρ]ᵇ p := by simp [interp]

theorem Sentence.interp_neg :
  𝓢 ⊨ₛ ~ p ↔ ¬ 𝓢 ⊨ₛ p := BFormula.interp_neg

theorem BFormula.val_interp_eq {ρ : 𝓢.BAssignment m} :
  (∀ x, ρ x = ρ' x) → (𝓢 ⊨[ρ]ᵇ p ↔ 𝓢 ⊨[ρ'] p.val) := by
  intro h
  induction p generalizing ρ' with simp [interp, Formula.interp]
  | rel r v => simp [BTerm.val_interp_eq h]
  | eq t₁ t₂ => simp [BTerm.val_interp_eq h]
  | imp p q ih₁ ih₂ => simp [ih₁ h, ih₂ h]
  | all p ih =>
    apply forall_congr'
    intro u; rw [ih]
    · intro x
      cases x using Fin.cases
      · rfl
      · simp [Assignment.cons]; apply h

theorem Sentence.val_interp_eq : 𝓢 ⊨ₛ p ↔ 𝓢 ⊨[ρ] p.val :=
  BFormula.val_interp_eq (·.elim0)



namespace Context

def Satisfiable (Γ : 𝓛.Context) :=
  ∃ (𝓢 : Structure.{u} 𝓛), ∃ ρ, ∀ p ∈ Γ, 𝓢 ⊨[ρ] p

theorem Satisfiable.weaken :
  Γ ⊆ Δ → Satisfiable.{u} Δ → Satisfiable.{u} Γ := by
  rintro h₁ ⟨𝓢, ⟨ρ, h₂⟩⟩
  exists 𝓢, ρ
  intros p h₃
  apply h₂
  apply h₁
  exact h₃

theorem Consistent.of_satisfiable {Γ : 𝓛.Context} :
  Γ.Satisfiable → Γ.Consistent := by
  intro ⟨𝓢, ρ, h₁⟩ h₂
  apply soundness at h₂
  apply h₂ at h₁
  exact h₁

end Context



namespace Structure

def ulift (𝓢 : Structure.{u₁} 𝓛) : Structure.{max u₁ u₂} 𝓛 where
  𝓤 := ULift.{u₂} 𝓢.𝓤
  inhabited𝓤 := ⟨ULift.up default⟩
  interp𝓕 := λ f v => ULift.up (𝓢.interp𝓕 f (ULift.down ∘ v))
  interp𝓡 := λ p v => 𝓢.interp𝓡 p (ULift.down ∘ v)

def Assignment.ulift (ρ : Assignment 𝓢) : Assignment (𝓢.ulift) :=
  λ x => ULift.up (ρ x)

lemma Assignment.ulift_cons {𝓢 : 𝓛.Structure} {ρ : 𝓢.Assignment} {u : 𝓢.𝓤} :
  (u ∷ₐ ρ).ulift = Assignment.cons (𝓢 := 𝓢.ulift) (ULift.up u) ρ.ulift := by
  funext x; cases x <;> rfl

end Structure

lemma Term.interp_ulift {𝓢 : 𝓛.Structure} {ρ : 𝓢.Assignment} :
  ⟦ t ⟧ₜ 𝓢.ulift, ρ.ulift = ULift.up (⟦ t ⟧ₜ 𝓢, ρ) := by
  induction t with simp [interp]
  | var => simp [Assignment.ulift]
  | func f v ih => simp [ih]; rfl

lemma Formula.interp_ulift {𝓢 : Structure 𝓛} {ρ : Assignment 𝓢} :
  𝓢.ulift ⊨[ρ.ulift] p ↔ 𝓢 ⊨[ρ] p := by
  induction p generalizing ρ with simp [interp]
  | rel r v => simp [Term.interp_ulift]; rfl
  | eq t₁ t₂ => simp [Term.interp_ulift]; exact ULift.up_inj
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih =>
    constructor
    · intros h u
      rw [←ih, Assignment.ulift_cons]
      apply h
    · intros h u
      rw [←ULift.up_down u, ←Assignment.ulift_cons, ih]
      apply h

theorem Entails.down : Γ ⊨.{max u₁ u₂} p → Γ ⊨.{u₁} p := by
  intros h 𝓢 ρ h₁
  have h₂ := h (Structure.ulift.{u₁,u₂} 𝓢) ρ.ulift
  simp [Formula.interp_ulift] at h₂
  exact h₂ h₁

theorem Context.Satisfiable.up :
  Satisfiable.{u₁} Γ → Satisfiable.{max u₁ u₂} Γ := by
  intro h
  rcases h with ⟨𝓢, ρ, h⟩
  exists (Structure.ulift.{u₁,u₂} 𝓢), ρ.ulift
  simp [Formula.interp_ulift]
  exact h



namespace Structure

variable {𝓜 𝓝 𝓢 : 𝓛.Structure}

def ElementaryEquivalent (𝓜 𝓝 : 𝓛.Structure) :=
  ∀ (p : 𝓛.Sentence), 𝓜 ⊨ₛ p ↔ 𝓝 ⊨ₛ p
infixr:25 " ≃ᴱ " => ElementaryEquivalent

structure Embedding (𝓜 𝓝 : 𝓛.Structure) extends 𝓜.𝓤 ↪ 𝓝.𝓤 where
  to_func : ∀ (f : 𝓛.𝓕 n) (v : Vec 𝓜.𝓤 n), toEmbedding (𝓜.interp𝓕 f v) = 𝓝.interp𝓕 f (toEmbedding ∘ v)
  to_rel : ∀ (r : 𝓛.𝓡 n) (v : Vec 𝓜.𝓤 n), 𝓜.interp𝓡 r v ↔ 𝓝.interp𝓡 r (toEmbedding ∘ v)
infixr:25 " ↪ᴹ " => Embedding

namespace Embedding

instance : CoeFun (𝓜 ↪ᴹ 𝓝) (λ _ => 𝓜.𝓤 → 𝓝.𝓤) := ⟨(·.toEmbedding)⟩

def refl : 𝓜 ↪ᴹ 𝓜 where
  toEmbedding := .refl 𝓜.𝓤
  to_func f v := rfl
  to_rel r v := by rfl

def trans (e₁ : 𝓜 ↪ᴹ 𝓝) (e₂ : 𝓝 ↪ᴹ 𝓢) : 𝓜 ↪ᴹ 𝓢 where
  toEmbedding := .trans e₁.toEmbedding e₂.toEmbedding
  to_func f v := by simp [Function.comp, e₁.to_func, e₂.to_func]
  to_rel r v := by simp [Function.comp]; rw [e₁.to_rel, e₂.to_rel]; rfl

theorem to_term (e : 𝓜 ↪ᴹ 𝓝) (t : 𝓛.Term) (ρ : 𝓜.Assignment) : e (⟦t⟧ₜ 𝓜, ρ) = ⟦t⟧ₜ 𝓝, e ∘ ρ := by
  induction t with simp [Term.interp]
  | func f v ih => rw [e.to_func]; congr; ext; simp [ih]

end Embedding

structure Isomorphism (𝓜 𝓝 : 𝓛.Structure) extends 𝓜.𝓤 ≃ 𝓝.𝓤 where
  to_func : ∀ (f : 𝓛.𝓕 n) (v : Vec 𝓜.𝓤 n), toEquiv (𝓜.interp𝓕 f v) = 𝓝.interp𝓕 f (toEquiv ∘ v)
  to_rel : ∀ (r : 𝓛.𝓡 n) (v : Vec 𝓜.𝓤 n), 𝓜.interp𝓡 r v ↔ 𝓝.interp𝓡 r (toEquiv ∘ v)
infixr:25 " ≃ᴹ " => Isomorphism

namespace Isomorphism

instance : CoeFun (𝓜 ≃ᴹ 𝓝) (λ _ => 𝓜.𝓤 → 𝓝.𝓤) := ⟨(·.toEquiv)⟩

def toEmbedding (i : 𝓜 ≃ᴹ 𝓝) : 𝓜 ↪ᴹ 𝓝 where
  toEmbedding := i.toEquiv.toEmbedding
  to_func := i.to_func
  to_rel := i.to_rel

def refl : 𝓜 ≃ᴹ 𝓜 where
  toEquiv := .refl 𝓜.𝓤
  to_func f v := rfl
  to_rel r v := by rfl

def symm (i : 𝓜 ≃ᴹ 𝓝) : 𝓝 ≃ᴹ 𝓜 where
  toEquiv := .symm i.toEquiv
  to_func f v := by apply i.toEquiv.injective; simp [Function.comp, i.to_func]
  to_rel r v := by rw [i.to_rel]; simp [Function.comp]

def trans (i₁ : 𝓜 ≃ᴹ 𝓝) (i₂ : 𝓝 ≃ᴹ 𝓢) : 𝓜 ≃ᴹ 𝓢 where
  toEquiv := .trans i₁.toEquiv i₂.toEquiv
  to_func f v := by simp [Function.comp, i₁.to_func, i₂.to_func]
  to_rel r v := by rw [i₁.to_rel, i₂.to_rel]; simp [Function.comp]

theorem to_term (i : 𝓜 ≃ᴹ 𝓝) (t : 𝓛.Term) (ρ : 𝓜.Assignment) : i (⟦t⟧ₜ 𝓜, ρ) = ⟦t⟧ₜ 𝓝, i ∘ ρ := by
  induction t with simp [Term.interp]
  | func f v ih => rw [i.to_func]; congr; ext; simp [ih]

theorem to_formula (e : 𝓜 ≃ᴹ 𝓝) (p : 𝓛.Formula) (ρ : 𝓜.Assignment) : 𝓜 ⊨[ρ] p ↔ 𝓝 ⊨[e ∘ ρ] p := by
  induction p generalizing ρ with simp [Formula.interp]
  | rel r v => rw [e.to_rel]; congr!; simp [e.to_term]
  | eq t₁ t₂ => simp [←e.to_term]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih =>
    simp [ih]
    rw [e.toEquiv.forall_congr]
    congr!
    funext x; cases x <;> simp [Function.comp, Assignment.cons]

theorem elementary_equivalent : (𝓜 ≃ᴹ 𝓝) → 𝓜 ≃ᴱ 𝓝 := by
  intro i p; rw [Sentence.val_interp_eq (ρ := default), Sentence.val_interp_eq]; apply i.to_formula

end Isomorphism

end Structure

end FirstOrder.Language
