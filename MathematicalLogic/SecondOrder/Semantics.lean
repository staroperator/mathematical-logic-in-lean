import MathematicalLogic.SecondOrder.Syntax

universe u

namespace SecondOrder.Language

structure Structure (L : Language) where
  Dom : Type u
  interpFunc : L.Func n → Vec Dom n → Dom
  interpRel : L.Rel n → Vec Dom n → Prop

variable {L : Language}

namespace Structure

variable {M : L.Structure}

instance : CoeSort L.Structure (Type u) := ⟨(·.Dom)⟩

@[reducible] def interpTy (M : L.Structure) : Ty → Type u
| Ty.var => M
| Ty.func n => Vec M n → M
| Ty.rel n => Vec M n → Prop

def Assignment (M: L.Structure) (Γ : List Ty) := ⦃T : Ty⦄ → Γ.Fin T → M.interpTy T

def Assignment.nil : M.Assignment [] := by rintro _ ⟨⟩
notation "[]ₐ" => Assignment.nil

def Assignment.cons (u : M.interpTy T) (ρ : M.Assignment Γ) : M.Assignment (T :: Γ)
| _, .fz => u
| _, .fs x => ρ x
infixr:80 " ∷ₐ " => Assignment.cons

def interp (M : L.Structure) {Γ} (ρ : M.Assignment Γ) : L.Term Γ → M
| #x => ρ x
| f ⬝ᶠ v => M.interpFunc f λ i => M.interp ρ (v i)
| f ⬝ᶠᵛ v => ρ f λ i => M.interp ρ (v i)
notation:80 "⟦ " t " ⟧ₜ " M ", " ρ:80 => interp M ρ t
@[simp] theorem interp_var : ⟦ #x ⟧ₜ M, ρ = ρ x := rfl
@[simp] theorem interp_fconst : ⟦ f ⬝ᶠ v ⟧ₜ M, ρ = M.interpFunc f λ i => ⟦ v i ⟧ₜ M, ρ := rfl
@[simp] theorem interp_fvar : ⟦ f ⬝ᶠᵛ v ⟧ₜ M, ρ = ρ f λ i => ⟦ v i ⟧ₜ M, ρ := rfl

def satisfy (M : L.Structure) (ρ : M.Assignment Γ) : L.Formula Γ → Prop
| r ⬝ʳ v => M.interpRel r λ i => ⟦ v i ⟧ₜ M, ρ
| r ⬝ʳᵛ v => ρ r λ i => ⟦ v i ⟧ₜ M, ρ
| t₁ ≐ t₂ => ⟦ t₁ ⟧ₜ M, ρ = ⟦ t₂ ⟧ₜ M, ρ
| ⊥ => False
| p ⇒ q => M.satisfy ρ p → M.satisfy ρ q
| ∀' p => ∀ (u : M), M.satisfy (u ∷ₐ ρ) p
| ∀ᶠ n p => ∀ (f : Vec M n → M), M.satisfy (f ∷ₐ ρ) p
| ∀ʳ n p => ∀ (r : Vec M n → Prop), M.satisfy (r ∷ₐ ρ) p
notation:50 M " ⊨[" ρ "] " p:50 => satisfy M ρ p
@[simp] theorem satisfy_rconst : M ⊨[ρ] r ⬝ʳ v ↔ M.interpRel r λ i => ⟦ v i ⟧ₜ M, ρ := by rfl
@[simp] theorem satisfy_rvar : M ⊨[ρ] r ⬝ʳᵛ v ↔ ρ r λ i => ⟦ v i ⟧ₜ M, ρ := by rfl
@[simp] theorem satisfy_eq : M ⊨[ρ] t₁ ≐ t₂ ↔ ⟦ t₁ ⟧ₜ M, ρ = ⟦ t₂ ⟧ₜ M, ρ := by rfl
@[simp] theorem satisfy_false : ¬ M ⊨[ρ] ⊥ := by tauto
@[simp] theorem satisfy_imp : M ⊨[ρ] p ⇒ q ↔ M ⊨[ρ] p → M ⊨[ρ] q := by rfl
@[simp] theorem satisfy_true : M ⊨[ρ] ⊤ := by tauto
@[simp] theorem satisfy_neg : M ⊨[ρ] ~ p ↔ ¬ M ⊨[ρ] p := by rfl
@[simp] theorem satisfy_and : M ⊨[ρ] p ⩑ q ↔ M ⊨[ρ] p ∧ M ⊨[ρ] q := by simp [ClassicalPropNotation.and_def]
@[simp] theorem satisfy_or : M ⊨[ρ] p ⩒ q ↔ M ⊨[ρ] p ∨ M ⊨[ρ] q := by simp [ClassicalPropNotation.or_def]; tauto
@[simp] theorem satisfy_iff : M ⊨[ρ] p ⇔ q ↔ (M ⊨[ρ] p ↔ M ⊨[ρ] q) := by simp [ClassicalPropNotation.iff_def]; tauto
@[simp] theorem satisfy_all : M ⊨[ρ] ∀' p ↔ ∀ (u : M), M ⊨[u ∷ₐ ρ] p := by rfl
@[simp] theorem satisfy_allf : M ⊨[ρ] ∀ᶠ n p ↔ ∀ (f : Vec M n → M), M ⊨[f ∷ₐ ρ] p := by rfl
@[simp] theorem satisfy_allr : M ⊨[ρ] ∀ʳ n p ↔ ∀ (r : Vec M n → Prop), M ⊨[r ∷ₐ ρ] p := by rfl
@[simp] theorem satisfy_ex : M ⊨[ρ] ∃' p ↔ ∃ (u : M), M ⊨[u ∷ₐ ρ] p := by simp [Formula.ex]
@[simp] theorem satisfy_exf : M ⊨[ρ] ∃ᶠ n p ↔ ∃ (f : Vec M n → M), M ⊨[f ∷ₐ ρ] p := by simp [Formula.exf]
@[simp] theorem satisfy_exr : M ⊨[ρ] ∃ʳ n p ↔ ∃ (r : Vec M n → Prop), M ⊨[r ∷ₐ ρ] p := by simp [Formula.exr]

abbrev satisfySentence (M : L.Structure) (p : L.Sentence) :=
  M ⊨[[]ₐ] p
infix:50 " ⊨ₛ " => satisfySentence

structure Embedding (M : L.Structure) (N : L.Structure) extends M ↪ N where
  on_func : ∀ (f : L.Func n) (v : Vec M n), toEmbedding (M.interpFunc f v) = N.interpFunc f (toEmbedding ∘ v)
  on_rel : ∀ (r : L.Rel n) (v : Vec M n), M.interpRel r v ↔ N.interpRel r (toEmbedding ∘ v)
infixr:25 " ↪ᴹ " => Embedding

namespace Embedding

instance : CoeFun (M ↪ᴹ N) (λ _ => M → N) := ⟨(·.toEmbedding)⟩

def refl : M ↪ᴹ M where
  toEmbedding := .refl M
  on_func f v := rfl
  on_rel r v := by rfl

def trans (e₁ : M ↪ᴹ N) (e₂ : N ↪ᴹ 𝓢) : M ↪ᴹ 𝓢 where
  toEmbedding := .trans e₁.toEmbedding e₂.toEmbedding
  on_func f v := by simp [e₁.on_func, e₂.on_func]; rfl
  on_rel r v := by rw [e₁.on_rel, e₂.on_rel]; rfl

end Embedding

structure Isomorphism (M : L.Structure) (N : L.Structure) extends M ≃ N where
  on_func : ∀ (f : L.Func n) (v : Vec M n), toEquiv (M.interpFunc f v) = N.interpFunc f (toEquiv ∘ v)
  on_rel : ∀ (r : L.Rel n) (v : Vec M n), M.interpRel r v ↔ N.interpRel r (toEquiv ∘ v)
infix:25 " ≃ᴹ " => Isomorphism

namespace Isomorphism

instance : CoeFun (M ≃ᴹ N) (λ _ => M → N) := ⟨(·.toEquiv)⟩

def refl : M ≃ᴹ M where
  toEquiv := .refl M
  on_func f v := rfl
  on_rel r v := by rfl

def symm (i : M ≃ᴹ N) : N ≃ᴹ M where
  toEquiv := .symm i.toEquiv
  on_func f v := by apply i.toEquiv.injective; rw [i.on_func]; simp [Function.comp_def]
  on_rel r v := by rw [i.on_rel]; simp [Function.comp_def]

def trans (i₁ : M ≃ᴹ N) (i₂ : N ≃ᴹ 𝓢) : M ≃ᴹ 𝓢 where
  toEquiv := .trans i₁.toEquiv i₂.toEquiv
  on_func f v := by simp [i₁.on_func, i₂.on_func]; rfl
  on_rel r v := by rw [i₁.on_rel, i₂.on_rel]; rfl

def toEmbedding (i : M ≃ᴹ N) : M ↪ᴹ N where
  toEmbedding := i.toEquiv
  on_func := i.on_func
  on_rel := i.on_rel

def onTy (i : M ≃ᴹ N) : {T : Ty} → M.interpTy T → N.interpTy T
| .var, x => i x
| .func _, f => λ v => i (f (i.symm ∘ v))
| .rel _, r => λ v => r (i.symm ∘ v)

def onAssignment (i : M ≃ᴹ N) : M.Assignment Γ → N.Assignment Γ :=
  λ ρ _ x => i.onTy (ρ x)

theorem on_term (i : M ≃ᴹ N) (t : L.Term Γ) (ρ : M.Assignment Γ) :
  i (⟦t⟧ₜ M, ρ) = ⟦t⟧ₜ N, i.onAssignment ρ := by
  induction t with simp [onAssignment, onTy]
  | fconst f v ih => rw [i.on_func]; congr; ext; simp [ih]
  | fvar f v ih => congr!; simp [←ih, symm]

theorem on_formula (i : M ≃ᴹ N) (p : L.Formula Γ) (ρ : M.Assignment Γ) :
  M ⊨[ρ] p ↔ N ⊨[i.onAssignment ρ] p := by
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

structure Model (T : L.Theory) extends L.Structure where
  satisfy_theory : ∀ p ∈ T, toStructure ⊨ₛ p

instance {T : L.Theory} : CoeOut T.Model L.Structure := ⟨(·.toStructure)⟩
instance {T : L.Theory} : CoeSort T.Model (Type u) := ⟨(·.Dom)⟩

def Entails (T : L.Theory) (p : L.Sentence) :=
  ∀ (M : Model.{u} T), M ⊨ₛ p
infix:50 " ⊨ " => Entails

def Categorical (T : L.Theory) :=
  ∀ (M : T.Model) (N : T.Model), M ≃ᴹ N.toStructure

end SecondOrder.Language.Theory
