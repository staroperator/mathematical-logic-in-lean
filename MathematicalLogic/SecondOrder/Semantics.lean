import MathematicalLogic.SecondOrder.Syntax

universe u

namespace SecondOrder.Language

structure Structure (𝓛 : Language) where
  Dom : Type u
  interpFunc : 𝓛.Func n → Vec Dom n → Dom
  interpRel : 𝓛.Rel n → Vec Dom n → Prop

variable {𝓛 : Language}

namespace Structure

variable {𝓜 : 𝓛.Structure}

instance : CoeSort 𝓛.Structure (Type u) := ⟨(·.Dom)⟩

@[reducible] def interpTy (𝓜 : 𝓛.Structure) : Ty → Type u
| Ty.var => 𝓜
| Ty.func n => Vec 𝓜 n → 𝓜
| Ty.rel n => Vec 𝓜 n → Prop

def Assignment (𝓜: 𝓛.Structure) (Γ : List Ty) := ⦃T : Ty⦄ → Γ.Fin T → 𝓜.interpTy T

def Assignment.nil : 𝓜.Assignment [] := by rintro _ ⟨⟩
notation "[]ₐ" => Assignment.nil

def Assignment.cons (u : 𝓜.interpTy T) (ρ : 𝓜.Assignment Γ) : 𝓜.Assignment (T :: Γ)
| _, .fz => u
| _, .fs x => ρ x
infixr:80 " ∷ₐ " => Assignment.cons

def interp (𝓜 : 𝓛.Structure) {Γ} (ρ : 𝓜.Assignment Γ) : 𝓛.Term Γ → 𝓜
| #x => ρ x
| f ⬝ᶠ v => 𝓜.interpFunc f λ i => 𝓜.interp ρ (v i)
| f ⬝ᶠᵛ v => ρ f λ i => 𝓜.interp ρ (v i)
notation:80 "⟦ " t " ⟧ₜ " 𝓜 ", " ρ:80 => interp 𝓜 ρ t
@[simp] theorem interp_var : ⟦ #x ⟧ₜ 𝓜, ρ = ρ x := rfl
@[simp] theorem interp_fconst : ⟦ f ⬝ᶠ v ⟧ₜ 𝓜, ρ = 𝓜.interpFunc f λ i => ⟦ v i ⟧ₜ 𝓜, ρ := rfl
@[simp] theorem interp_fvar : ⟦ f ⬝ᶠᵛ v ⟧ₜ 𝓜, ρ = ρ f λ i => ⟦ v i ⟧ₜ 𝓜, ρ := rfl

def satisfy (𝓜 : 𝓛.Structure) (ρ : 𝓜.Assignment Γ) : 𝓛.Formula Γ → Prop
| r ⬝ʳ v => 𝓜.interpRel r λ i => ⟦ v i ⟧ₜ 𝓜, ρ
| r ⬝ʳᵛ v => ρ r λ i => ⟦ v i ⟧ₜ 𝓜, ρ
| t₁ ≐ t₂ => ⟦ t₁ ⟧ₜ 𝓜, ρ = ⟦ t₂ ⟧ₜ 𝓜, ρ
| ⊥ => False
| p ⇒ q => 𝓜.satisfy ρ p → 𝓜.satisfy ρ q
| ∀' p => ∀ (u : 𝓜), 𝓜.satisfy (u ∷ₐ ρ) p
| ∀ᶠ n p => ∀ (f : Vec 𝓜 n → 𝓜), 𝓜.satisfy (f ∷ₐ ρ) p
| ∀ʳ n p => ∀ (r : Vec 𝓜 n → Prop), 𝓜.satisfy (r ∷ₐ ρ) p
notation:50 𝓜 " ⊨[" ρ "] " p:50 => satisfy 𝓜 ρ p
@[simp] theorem satisfy_rconst : 𝓜 ⊨[ρ] r ⬝ʳ v ↔ 𝓜.interpRel r λ i => ⟦ v i ⟧ₜ 𝓜, ρ := by rfl
@[simp] theorem satisfy_rvar : 𝓜 ⊨[ρ] r ⬝ʳᵛ v ↔ ρ r λ i => ⟦ v i ⟧ₜ 𝓜, ρ := by rfl
@[simp] theorem satisfy_eq : 𝓜 ⊨[ρ] t₁ ≐ t₂ ↔ ⟦ t₁ ⟧ₜ 𝓜, ρ = ⟦ t₂ ⟧ₜ 𝓜, ρ := by rfl
@[simp] theorem satisfy_false : ¬ 𝓜 ⊨[ρ] ⊥ := by simp [satisfy]
@[simp] theorem satisfy_imp : 𝓜 ⊨[ρ] p ⇒ q ↔ 𝓜 ⊨[ρ] p → 𝓜 ⊨[ρ] q := by rfl
@[simp] theorem satisfy_true : 𝓜 ⊨[ρ] ⊤ := by simp [satisfy]
@[simp] theorem satisfy_and : 𝓜 ⊨[ρ] p ⩑ q ↔ 𝓜 ⊨[ρ] p ∧ 𝓜 ⊨[ρ] q := by simp [satisfy]
@[simp] theorem satisfy_or : 𝓜 ⊨[ρ] p ⩒ q ↔ 𝓜 ⊨[ρ] p ∨ 𝓜 ⊨[ρ] q := by simp [satisfy]; tauto
@[simp] theorem satisfy_iff : 𝓜 ⊨[ρ] p ⇔ q ↔ (𝓜 ⊨[ρ] p ↔ 𝓜 ⊨[ρ] q) := by simp [satisfy]; tauto
@[simp] theorem satisfy_all : 𝓜 ⊨[ρ] ∀' p ↔ ∀ (u : 𝓜), 𝓜 ⊨[u ∷ₐ ρ] p := by rfl
@[simp] theorem satisfy_allf : 𝓜 ⊨[ρ] ∀ᶠ n p ↔ ∀ (f : Vec 𝓜 n → 𝓜), 𝓜 ⊨[f ∷ₐ ρ] p := by rfl
@[simp] theorem satisfy_allr : 𝓜 ⊨[ρ] ∀ʳ n p ↔ ∀ (r : Vec 𝓜 n → Prop), 𝓜 ⊨[r ∷ₐ ρ] p := by rfl
@[simp] theorem satisfy_ex : 𝓜 ⊨[ρ] ∃' p ↔ ∃ (u : 𝓜), 𝓜 ⊨[u ∷ₐ ρ] p := by simp [satisfy]
@[simp] theorem satisfy_exf : 𝓜 ⊨[ρ] ∃ᶠ n p ↔ ∃ (f : Vec 𝓜 n → 𝓜), 𝓜 ⊨[f ∷ₐ ρ] p := by simp [satisfy]
@[simp] theorem satisfy_exr : 𝓜 ⊨[ρ] ∃ʳ n p ↔ ∃ (r : Vec 𝓜 n → Prop), 𝓜 ⊨[r ∷ₐ ρ] p := by simp [satisfy]

abbrev satisfySentence (𝓜 : 𝓛.Structure) (p : 𝓛.Sentence) :=
  𝓜 ⊨[[]ₐ] p
infix:50 " ⊨ₛ " => satisfySentence

structure Embedding (𝓜 : 𝓛.Structure) (𝓝 : 𝓛.Structure) extends 𝓜 ↪ 𝓝 where
  on_func : ∀ (f : 𝓛.Func n) (v : Vec 𝓜 n), toEmbedding (𝓜.interpFunc f v) = 𝓝.interpFunc f (toEmbedding ∘ v)
  on_rel : ∀ (r : 𝓛.Rel n) (v : Vec 𝓜 n), 𝓜.interpRel r v ↔ 𝓝.interpRel r (toEmbedding ∘ v)
infixr:25 " ↪ᴹ " => Embedding

namespace Embedding

instance : CoeFun (𝓜 ↪ᴹ 𝓝) (λ _ => 𝓜 → 𝓝) := ⟨(·.toEmbedding)⟩

def refl : 𝓜 ↪ᴹ 𝓜 where
  toEmbedding := .refl 𝓜
  on_func f v := rfl
  on_rel r v := by rfl

def trans (e₁ : 𝓜 ↪ᴹ 𝓝) (e₂ : 𝓝 ↪ᴹ 𝓢) : 𝓜 ↪ᴹ 𝓢 where
  toEmbedding := .trans e₁.toEmbedding e₂.toEmbedding
  on_func f v := by simp [e₁.on_func, e₂.on_func]; rfl
  on_rel r v := by rw [e₁.on_rel, e₂.on_rel]; rfl

end Embedding

structure Isomorphism (𝓜 : 𝓛.Structure) (𝓝 : 𝓛.Structure) extends 𝓜 ≃ 𝓝 where
  on_func : ∀ (f : 𝓛.Func n) (v : Vec 𝓜 n), toEquiv (𝓜.interpFunc f v) = 𝓝.interpFunc f (toEquiv ∘ v)
  on_rel : ∀ (r : 𝓛.Rel n) (v : Vec 𝓜 n), 𝓜.interpRel r v ↔ 𝓝.interpRel r (toEquiv ∘ v)
infix:25 " ≃ᴹ " => Isomorphism

namespace Isomorphism

instance : CoeFun (𝓜 ≃ᴹ 𝓝) (λ _ => 𝓜 → 𝓝) := ⟨(·.toEquiv)⟩

def refl : 𝓜 ≃ᴹ 𝓜 where
  toEquiv := .refl 𝓜
  on_func f v := rfl
  on_rel r v := by rfl

def symm (i : 𝓜 ≃ᴹ 𝓝) : 𝓝 ≃ᴹ 𝓜 where
  toEquiv := .symm i.toEquiv
  on_func f v := by apply i.toEquiv.injective; rw [i.on_func]; simp [Function.comp_def]
  on_rel r v := by rw [i.on_rel]; simp [Function.comp_def]

def trans (i₁ : 𝓜 ≃ᴹ 𝓝) (i₂ : 𝓝 ≃ᴹ 𝓢) : 𝓜 ≃ᴹ 𝓢 where
  toEquiv := .trans i₁.toEquiv i₂.toEquiv
  on_func f v := by simp [i₁.on_func, i₂.on_func]; rfl
  on_rel r v := by rw [i₁.on_rel, i₂.on_rel]; rfl

def toEmbedding (i : 𝓜 ≃ᴹ 𝓝) : 𝓜 ↪ᴹ 𝓝 where
  toEmbedding := i.toEquiv
  on_func := i.on_func
  on_rel := i.on_rel

def onTy (i : 𝓜 ≃ᴹ 𝓝) : {T : Ty} → 𝓜.interpTy T → 𝓝.interpTy T
| .var, x => i x
| .func _, f => λ v => i (f (i.symm ∘ v))
| .rel _, r => λ v => r (i.symm ∘ v)

def onAssignment (i : 𝓜 ≃ᴹ 𝓝) : 𝓜.Assignment Γ → 𝓝.Assignment Γ :=
  λ ρ _ x => i.onTy (ρ x)

theorem on_term (i : 𝓜 ≃ᴹ 𝓝) (t : 𝓛.Term Γ) (ρ : 𝓜.Assignment Γ) :
  i (⟦t⟧ₜ 𝓜, ρ) = ⟦t⟧ₜ 𝓝, i.onAssignment ρ := by
  induction t with simp [onAssignment, onTy]
  | fconst f v ih => rw [i.on_func]; congr; ext; simp [ih]
  | fvar f v ih => congr!; simp [←ih, symm]

theorem on_formula (i : 𝓜 ≃ᴹ 𝓝) (p : 𝓛.Formula Γ) (ρ : 𝓜.Assignment Γ) :
  𝓜 ⊨[ρ] p ↔ 𝓝 ⊨[i.onAssignment ρ] p := by
  induction p with simp [onAssignment, onTy]
  | rconst r v => rw [i.on_rel]; congr!; simp [i.on_term]
  | rvar r v => congr!; simp [←i.on_term, symm]
  | eq t₁ t₂ => simp [←i.on_term]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih =>
    simp [ih]
    rw [i.toEquiv.forall_congr]
    congr!
    funext _ x; cases x <;> simp [onAssignment, onTy, Assignment.cons]
  | allf n p ih =>
    constructor
    · intro h f
      have := h λ v => i.symm (f (i ∘ v))
      simp [ih] at this
      convert this
      funext _ x; cases x <;> simp [onAssignment, onTy, Assignment.cons, symm, Function.comp_def]
    · intro h f
      have := h λ v => i (f (i.symm ∘ v))
      simp [ih]
      convert this
      funext _ x; cases x <;> simp [onAssignment, onTy, Assignment.cons]
  | allr n p ih =>
    constructor
    · intro h r
      have := h λ v => r (i ∘ v)
      simp [ih] at this
      convert this
      funext _ x; cases x <;> simp [onAssignment, onTy, Assignment.cons, symm, Function.comp_def]
    · intro h r
      have := h λ v => r (i.symm ∘ v)
      simp [ih]
      convert this
      funext _ x; cases x <;> simp [onAssignment, onTy, Assignment.cons]

end Isomorphism

end Structure

namespace Theory

structure Model (𝓣 : 𝓛.Theory) extends 𝓛.Structure where
  satisfy_theory : ∀ p ∈ 𝓣, toStructure ⊨ₛ p

instance {𝓣 : 𝓛.Theory} : CoeOut 𝓣.Model 𝓛.Structure := ⟨(·.toStructure)⟩
instance {𝓣 : 𝓛.Theory} : CoeSort 𝓣.Model (Type u) := ⟨(·.Dom)⟩

def Entails (𝓣 : 𝓛.Theory) (p : 𝓛.Sentence) :=
  ∀ (𝓜 : Model.{u} 𝓣), 𝓜 ⊨ₛ p
infix:50 " ⊨ " => Entails

def Categorical (𝓣 : 𝓛.Theory) :=
  ∀ (𝓜 : 𝓣.Model) (𝓝 : 𝓣.Model), 𝓜 ≃ᴹ 𝓝.toStructure

end SecondOrder.Language.Theory
