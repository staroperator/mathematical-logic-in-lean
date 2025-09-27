import MathematicalLogic.SecondOrder.Syntax

universe u v

namespace SecondOrder.Language

class HasStructure (L : Language) (M : Type u) where
  interpFunc : L.Func n → Vec M n → M
  interpRel : L.Rel n → Vec M n → Prop

variable {L : Language}

def interpTy (M : Type u) : Ty → Type u
| .var => M
| .func n => Vec M n → M
| .rel n => Vec M n → Prop

def Assignment (M : Type u) (l : List Ty) := ⦃T : Ty⦄ → l.Fin T → interpTy M T

namespace Assignment

def nil : Assignment M [] := nofun
notation "[]ₐ" => Assignment.nil

def cons (u : interpTy M T) (ρ : Assignment M l) : Assignment M (T :: l)
| _, .fz => u
| _, .fs x => ρ x
infixr:80 " ∷ₐ " => Assignment.cons

@[simp] theorem cons_zero : (u ∷ₐ ρ) 0 = u := rfl
@[simp] theorem cons_one {ρ : Assignment M (T :: l)} : (u ∷ₐ ρ) 1 = (ρ 0 : interpTy M T) := rfl
@[simp] theorem cons_two {ρ : Assignment M (T₁ :: T₂ :: l)} : (u ∷ₐ ρ) 2 = (ρ 1 : interpTy M T₂) := rfl
@[simp] theorem cons_three {ρ : Assignment M (T₁ :: T₂ :: T₃ :: l)} : (u ∷ₐ ρ) 3 = (ρ 2 : interpTy M T₃) := rfl
@[simp] theorem cons_four {ρ : Assignment M (T₁ :: T₂ :: T₃ :: T₄ :: l)} : (u ∷ₐ ρ) 4 = (ρ 3 : interpTy M T₄) := rfl

end Assignment

open HasStructure

variable {M : Type u} [HasStructure L M] {l} {ρ : Assignment M l} {p q : L.Formula l}

def interp (M : Type u) [L.HasStructure M] (ρ : Assignment M l) : L.Term l → M
| #x => ρ x
| f ⬝ᶠ v => interpFunc f λ i => interp M ρ (v i)
| f ⬝ᶠᵛ v => ρ f λ i => interp M ρ (v i)
notation:55 "⟦ " t " ⟧ₜ " M ", " ρ:55 => interp M ρ t

@[simp] theorem interp_var : ⟦ (#x : L.Term l) ⟧ₜ M, ρ = ρ x := rfl
@[simp] theorem interp_fconst : ⟦ (f ⬝ᶠ v : L.Term l) ⟧ₜ M, ρ = interpFunc f λ i => ⟦ v i ⟧ₜ M, ρ := rfl
@[simp] theorem interp_fvar : ⟦ (f ⬝ᶠᵛ v : L.Term l) ⟧ₜ M, ρ = ρ f λ i => ⟦ v i ⟧ₜ M, ρ := rfl

def satisfy (M : Type u) [L.HasStructure M] : {l : List Ty} → L.Formula l → Assignment M l → Prop
| _, r ⬝ʳ v, ρ => interpRel r λ i => ⟦ v i ⟧ₜ M, ρ
| _, r ⬝ʳᵛ v, ρ => ρ r λ i => ⟦ v i ⟧ₜ M, ρ
| _, t₁ ≐ t₂, ρ => ⟦ t₁ ⟧ₜ M, ρ = ⟦ t₂ ⟧ₜ M, ρ
| _, ⊥, _ => False
| _, p ⇒ q, ρ => satisfy M p ρ → satisfy M q ρ
| _, ∀' p, ρ => ∀ (u : M), satisfy M p (u ∷ₐ ρ)
| _, ∀ᶠ[n] p, ρ => ∀ (f : Vec M n → M), satisfy M p (f ∷ₐ ρ)
| _, ∀ʳ[n] p, ρ => ∀ (r : Vec M n → Prop), satisfy M p (r ∷ₐ ρ)
notation:50 M " ⊨[" ρ "] " p:50 => satisfy M p ρ

@[simp] theorem satisfy_rconst : M ⊨[ρ] (r ⬝ʳ v : L.Formula l) ↔ interpRel r λ i => ⟦ v i ⟧ₜ M, ρ := by rfl
@[simp] theorem satisfy_rvar : M ⊨[ρ] (r ⬝ʳᵛ v : L.Formula l) ↔ ρ r λ i => ⟦ v i ⟧ₜ M, ρ := by rfl
@[simp] theorem satisfy_eq : M ⊨[ρ] (t₁ ≐ t₂ : L.Formula l) ↔ ⟦ t₁ ⟧ₜ M, ρ = ⟦ t₂ ⟧ₜ M, ρ := by rfl
@[simp] theorem satisfy_false : ¬ M ⊨[ρ] (⊥ : L.Formula l) := by tauto
@[simp] theorem satisfy_imp : M ⊨[ρ] p ⇒ q ↔ M ⊨[ρ] p → M ⊨[ρ] q := by rfl
@[simp] theorem satisfy_true : M ⊨[ρ] (⊤ : L.Formula l) := by tauto
@[simp] theorem satisfy_neg : M ⊨[ρ] ~ p ↔ ¬ M ⊨[ρ] p := by rfl
@[simp] theorem satisfy_and : M ⊨[ρ] p ⩑ q ↔ M ⊨[ρ] p ∧ M ⊨[ρ] q := by simp [ClassicalPropNotation.and_def]
@[simp] theorem satisfy_or : M ⊨[ρ] p ⩒ q ↔ M ⊨[ρ] p ∨ M ⊨[ρ] q := by simp [ClassicalPropNotation.or_def]; tauto
@[simp] theorem satisfy_iff : M ⊨[ρ] p ⇔ q ↔ (M ⊨[ρ] p ↔ M ⊨[ρ] q) := by simp [ClassicalPropNotation.iff_def]; tauto
@[simp] theorem satisfy_all {p : L.Formula (_ :: l)} : M ⊨[ρ] ∀' p ↔ ∀ (u : M), M ⊨[u ∷ₐ ρ] p := by rfl
@[simp] theorem satisfy_allf {p : L.Formula (_ :: l)} : M ⊨[ρ] ∀ᶠ[n] p ↔ ∀ (f : Vec M n → M), M ⊨[f ∷ₐ ρ] p := by rfl
@[simp] theorem satisfy_allr {p : L.Formula (_ :: l)} : M ⊨[ρ] ∀ʳ[n] p ↔ ∀ (r : Vec M n → Prop), M ⊨[r ∷ₐ ρ] p := by rfl
@[simp] theorem satisfy_ex {p : L.Formula (_ :: l)} : M ⊨[ρ] ∃' p ↔ ∃ (u : M), M ⊨[u ∷ₐ ρ] p := by simp [Formula.ex]
@[simp] theorem satisfy_exf {p : L.Formula (_ :: l)} : M ⊨[ρ] ∃ᶠ[n] p ↔ ∃ (f : Vec M n → M), M ⊨[f ∷ₐ ρ] p := by simp [Formula.exf]
@[simp] theorem satisfy_exr {p : L.Formula (_ :: l)} : M ⊨[ρ] ∃ʳ[n] p ↔ ∃ (r : Vec M n → Prop), M ⊨[r ∷ₐ ρ] p := by simp [Formula.exr]

abbrev satisfys (M : Type u) [L.HasStructure M] (p : L.Sentence) := M ⊨[[]ₐ] p
infix:50 " ⊨ₛ " => satisfys

structure Structure (L : Language) where
  Dom : Type u
  interpFunc : L.Func n → Vec Dom n → Dom
  interpRel : L.Rel n → Vec Dom n → Prop

namespace Structure

instance : CoeSort L.Structure (Type u) := ⟨(·.Dom)⟩
instance {M : L.Structure} : L.HasStructure M := ⟨M.interpFunc, M.interpRel⟩
@[reducible] def of (M : Type u) [L.HasStructure M] : L.Structure :=
  ⟨M, HasStructure.interpFunc, HasStructure.interpRel⟩

variable {M N : L.Structure}

structure Embedding (M : L.Structure) (N : L.Structure) extends M ↪ N where
  on_func : ∀ (f : L.Func n) (v : Vec M n), toEmbedding (HasStructure.interpFunc f v) = HasStructure.interpFunc f (toEmbedding ∘ v)
  on_rel : ∀ (r : L.Rel n) (v : Vec M n), HasStructure.interpRel r v ↔ HasStructure.interpRel r (toEmbedding ∘ v)
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
  on_func : ∀ (f : L.Func n) (v : Vec M n), toEquiv (HasStructure.interpFunc f v) = HasStructure.interpFunc f (toEquiv ∘ v)
  on_rel : ∀ (r : L.Rel n) (v : Vec M n), HasStructure.interpRel r v ↔ HasStructure.interpRel r (toEquiv ∘ v)
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

def onTy (i : M ≃ᴹ N) : {T : Ty} → interpTy M T → interpTy N T
| .var, x => i x
| .func _, f => λ v => i (f (i.symm ∘ v))
| .rel _, r => λ v => r (i.symm ∘ v)

def onAssignment (i : M ≃ᴹ N) : Assignment M l → Assignment N l :=
  λ ρ _ x => i.onTy (ρ x)

theorem on_term (i : M ≃ᴹ N) (t : L.Term l) (ρ : Assignment M l) :
  i (⟦t⟧ₜ M, ρ) = ⟦t⟧ₜ N, i.onAssignment ρ := by
  induction t with simp [onAssignment, onTy]
  | fconst f v ih => rw [i.on_func]; congr; ext; simp [ih]
  | fvar f v ih => congr!; simp [←ih, symm]

theorem on_formula (i : M ≃ᴹ N) (p : L.Formula l) (ρ : Assignment M l) :
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

class IsModel (T : L.Theory) (M : Type u) [L.HasStructure M] : Prop where
  satisfy_theory : ∀ p ∈ T, M ⊨ₛ p

structure Model (T : L.Theory) extends L.Structure where
  satisfy_theory :
    haveI : L.HasStructure toStructure := Structure.instHasStructureDom
    ∀ p ∈ T, toStructure ⊨ₛ p

variable {T : L.Theory} {M : T.Model} {p q : L.Sentence}

namespace Model

instance : CoeOut T.Model L.Structure := ⟨(·.toStructure)⟩
instance : CoeSort T.Model (Type u) := ⟨(·.Dom)⟩
instance : T.IsModel M := ⟨M.satisfy_theory⟩

@[reducible] def of (M : Type u) [L.HasStructure M] [T.IsModel M] : T.Model :=
  ⟨Structure.of M, IsModel.satisfy_theory⟩

end Model

def Categorical (T : L.Theory) :=
  ∀ (M : Model.{u} T) (N : Model.{v} T), Nonempty (M ≃ᴹ N.toStructure)

end SecondOrder.Language.Theory
