import MathematicalLogic.FirstOrder.Syntax

universe u v

namespace FirstOrder.Language

class IsStructure (𝓛 : Language) (𝓜 : Type u) where
  interpFunc : 𝓛.Func n → Vec 𝓜 n → 𝓜
  interpRel : 𝓛.Rel n → Vec 𝓜 n → Prop

variable {𝓛 : Language} {𝓜 : Type u} [𝓛.IsStructure 𝓜] {t t₁ t₂ : 𝓛.Term n} {p q : 𝓛.Formula n}

open IsStructure

def interp (𝓜 : Type u) [𝓛.IsStructure 𝓜] : 𝓛.Term n → Vec 𝓜 n → 𝓜
| #x, ρ => ρ x
| f ⬝ᶠ v, ρ => interpFunc f λ i => interp 𝓜 (v i) ρ
notation:80 "⟦" t "⟧ₜ " α ", " ρ:80 => interp α t ρ

@[simp] theorem interp_var : ⟦ (#x : 𝓛.Term n) ⟧ₜ 𝓜, ρ = ρ x := rfl
@[simp] theorem interp_func : ⟦ (f ⬝ᶠ v : 𝓛.Term n) ⟧ₜ 𝓜, ρ = interpFunc f λ i => ⟦ v i ⟧ₜ 𝓜, ρ := rfl

theorem interp_subst : ⟦ t[σ]ₜ ⟧ₜ 𝓜, ρ = ⟦ t ⟧ₜ 𝓜, λ x => ⟦ σ x ⟧ₜ 𝓜, ρ := by
  induction t with simp
  | func f v ih => simp [ih]

theorem interp_shift : ⟦ ↑ₜt ⟧ₜ 𝓜, (u ∷ᵥ ρ) = ⟦ t ⟧ₜ 𝓜, ρ := by
  simp [Term.shift, interp_subst]

def satisfy (𝓜 : Type u) [𝓛.IsStructure 𝓜] : {n : ℕ} → 𝓛.Formula n → Vec 𝓜 n → Prop
| _, r ⬝ʳ v, ρ => interpRel r λ i => ⟦ v i ⟧ₜ 𝓜, ρ
| _, t₁ ≐ t₂, ρ => ⟦ t₁ ⟧ₜ 𝓜, ρ = ⟦ t₂ ⟧ₜ 𝓜, ρ
| _, ⊥, _ => False
| _, p ⇒ q, ρ => satisfy 𝓜 p ρ → satisfy 𝓜 q ρ
| _, ∀' p, ρ => ∀ u, satisfy 𝓜 p (u ∷ᵥ ρ)
notation:50 𝓜 " ⊨[" ρ "] " p:50 => satisfy 𝓜 p ρ

@[simp] theorem satisfy_rel : 𝓜 ⊨[ρ] (r ⬝ʳ v : 𝓛.Formula n) ↔ interpRel r λ i => ⟦ v i ⟧ₜ 𝓜, ρ := by rfl
@[simp] theorem satisfy_eq : 𝓜 ⊨[ρ] t₁ ≐ t₂ ↔ ⟦ t₁ ⟧ₜ 𝓜, ρ = ⟦ t₂ ⟧ₜ 𝓜, ρ := by rfl
@[simp] theorem satisfy_false : ¬ 𝓜 ⊨[ρ] (⊥ : 𝓛.Formula n) := by tauto
@[simp] theorem satisfy_imp : 𝓜 ⊨[ρ] p ⇒ q ↔ 𝓜 ⊨[ρ] p → 𝓜 ⊨[ρ] q := by rfl
@[simp] theorem satisfy_true : 𝓜 ⊨[ρ] (⊤ : 𝓛.Formula n) := by tauto
@[simp] theorem satisfy_neg : 𝓜 ⊨[ρ] ~ p ↔ ¬ 𝓜 ⊨[ρ] p := by rfl
@[simp] theorem satisfy_and : 𝓜 ⊨[ρ] p ⩑ q ↔ 𝓜 ⊨[ρ] p ∧ 𝓜 ⊨[ρ] q := by simp [PropNotation.and]
@[simp] theorem satisfy_or : 𝓜 ⊨[ρ] p ⩒ q ↔ 𝓜 ⊨[ρ] p ∨ 𝓜 ⊨[ρ] q := by simp [PropNotation.or]; tauto
@[simp] theorem satisfy_iff : 𝓜 ⊨[ρ] p ⇔ q ↔ (𝓜 ⊨[ρ] p ↔ 𝓜 ⊨[ρ] q) := by simp [PropNotation.iff]; tauto
@[simp] theorem satisfy_all {p : 𝓛.Formula (n + 1)} : 𝓜 ⊨[ρ] ∀' p ↔ ∀ u, 𝓜 ⊨[u ∷ᵥ ρ] p := by rfl
@[simp] theorem satisfy_ex {p : 𝓛.Formula (n + 1)} : 𝓜 ⊨[ρ] ∃' p ↔ ∃ u, 𝓜 ⊨[u ∷ᵥ ρ] p := by simp [Formula.ex]

theorem satisfy_andN {v : Vec (𝓛.Formula n) m} :
  𝓜 ⊨[ρ] (⋀ i, v i) ↔ ∀ i, 𝓜 ⊨[ρ] v i := by
  induction m with simp [Formula.andN]
  | succ n ih => simp [Vec.head, ih, Fin.forall_fin_succ]

theorem satisfy_orN {v : Vec (𝓛.Formula n) m} :
  𝓜 ⊨[ρ] (⋁ i, v i) ↔ ∃ i, 𝓜 ⊨[ρ] v i := by
  induction m with simp [Formula.orN]
  | succ n ih => simp [Vec.head, ih, Fin.exists_fin_succ]

theorem satisfy_allN {p : 𝓛.Formula (n + m)} :
  𝓜 ⊨[ρ] ∀^[m] p ↔ ∀ v, 𝓜 ⊨[v ++ᵥ ρ] p := by
  induction m with simp [Formula.allN, Vec.eq_nil]
  | succ m ih =>
    rw [ih]; simp [Fin.forall_fin_succ_pi]; rw [forall_comm]; rfl

theorem satisfy_exN {p : 𝓛.Formula (n + m)} :
  𝓜 ⊨[ρ] ∃^[m] p ↔ ∃ v, 𝓜 ⊨[v ++ᵥ ρ] p := by
  induction m with simp [Formula.exN, Vec.eq_nil]
  | succ m ih =>
    rw [ih]; simp [Fin.exists_fin_succ_pi]; rw [exists_comm]; rfl

theorem satisfy_subst {σ : 𝓛.Subst n m} :
  𝓜 ⊨[ρ] p[σ]ₚ ↔ 𝓜 ⊨[λ x => ⟦ σ x ⟧ₜ 𝓜, ρ] p := by
  induction p generalizing m with simp
  | rel | eq => simp [interp_subst]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih =>
    apply forall_congr'
    intro u; simp [ih]
    congr! with x
    cases x using Fin.cases <;> simp [interp_shift]

theorem satisfy_subst_single {p : 𝓛.Formula (n + 1)} :
  𝓜 ⊨[ρ] p[↦ₛ t]ₚ ↔ 𝓜 ⊨[ ⟦t⟧ₜ 𝓜, ρ ∷ᵥ ρ ] p := by
  simp [satisfy_subst]
  congr! with x
  cases x using Fin.cases <;> simp

theorem satisfy_subst_assign {p : 𝓛.Formula (n + 1)} {t} :
  𝓜 ⊨[ρ] p[≔ₛ t]ₚ ↔ 𝓜 ⊨[ ⟦t⟧ₜ 𝓜, ρ ∷ᵥ ρ.tail ] p := by
  simp [satisfy_subst]
  congr! with x
  cases x using Fin.cases <;> simp

theorem satisfy_shift : 𝓜 ⊨[u ∷ᵥ ρ] ↑ₚp ↔ 𝓜 ⊨[ρ] p := by
  simp [Formula.shift, satisfy_subst]

abbrev satisfySentence (𝓜 : Type u) [𝓛.IsStructure 𝓜] (p : 𝓛.Sentence) := 𝓜 ⊨[[]ᵥ] p
infix:50 " ⊨ₛ " => satisfySentence

theorem satisfy_alls : 𝓜 ⊨ₛ ∀* p ↔ ∀ ρ, 𝓜 ⊨[ρ] p := by
  induction n with simp [Formula.alls]
  | zero => rfl
  | succ n ih =>
    simp [ih]
    constructor
    · intro h ρ; rw [Vec.eq_cons ρ]; apply h
    · intro h ρ u; exact h (u ∷ᵥ ρ)

structure Structure (𝓛 : Language) where
  Dom : Type u
  interpFunc {n} : 𝓛.Func n → Vec Dom n → Dom
  interpRel {n} : 𝓛.Rel n → Vec Dom n → Prop

namespace Structure

instance : CoeSort 𝓛.Structure (Type u) := ⟨(·.Dom)⟩
instance {𝓜 : 𝓛.Structure} : 𝓛.IsStructure 𝓜 := ⟨𝓜.interpFunc, 𝓜.interpRel⟩
@[reducible] def of (𝓜 : Type u) [𝓛.IsStructure 𝓜] : 𝓛.Structure := ⟨𝓜, IsStructure.interpFunc, IsStructure.interpRel⟩

end Structure



def Entails (Γ : 𝓛.FormulaSet n) (p : 𝓛.Formula n) :=
  ∀ (𝓜 : Structure.{u} 𝓛) (ρ), (∀ q ∈ Γ, 𝓜 ⊨[ρ] q) → 𝓜 ⊨[ρ] p

infix:50 " ⊨ " => Entails
syntax:50 term " ⊨.{" level "} " term:50 : term
macro_rules
| `($Γ ⊨.{$u} $p) => `(Entails.{$u} $Γ $p)

def Satisfiable (Γ : 𝓛.FormulaSet n) :=
  ∃ (𝓢 : Structure.{u} 𝓛), ∃ ρ, ∀ p ∈ Γ, 𝓢 ⊨[ρ] p

theorem Satisfiable.weaken :
  Γ ⊆ Δ → Satisfiable.{u} Δ → Satisfiable.{u} Γ := by
  rintro h₁ ⟨𝓢, ⟨ρ, h₂⟩⟩
  exists 𝓢, ρ
  intros p h₃
  apply h₂
  apply h₁
  exact h₃

namespace Theory

class IsModel (𝓣 : 𝓛.Theory) (𝓜 : Type u) [𝓛.IsStructure 𝓜] : Prop where
  satisfy_theory : ∀ p ∈ 𝓣, 𝓜 ⊨ₛ p

structure Model (𝓣 : 𝓛.Theory) extends 𝓛.Structure where
  satisfy_theory : ∀ p ∈ 𝓣, toStructure ⊨ₛ p

variable {𝓣 : 𝓛.Theory} {𝓜 : 𝓣.Model} {p q : 𝓛.Sentence}

namespace Model

instance : CoeOut 𝓣.Model 𝓛.Structure := ⟨(·.toStructure)⟩
instance : CoeSort 𝓣.Model (Type u) := ⟨(·.Dom)⟩
instance : 𝓣.IsModel 𝓜 := ⟨𝓜.satisfy_theory⟩

def of (𝓜 : Type u) [𝓛.IsStructure 𝓜] [𝓣.IsModel 𝓜] : 𝓣.Model := ⟨Structure.of 𝓜, IsModel.satisfy_theory⟩

end Model

theorem entails_iff : 𝓣 ⊨.{u} p ↔ ∀ (𝓜 : Model.{u} 𝓣), 𝓜 ⊨ₛ p := by
  constructor
  · intro h 𝓜; apply h; exact 𝓜.satisfy_theory
  · intro h 𝓜 ρ h₁; rw [Vec.eq_nil ρ] at *; exact h ⟨𝓜, h₁⟩

theorem satisfiable_iff : Satisfiable.{u} 𝓣 ↔ Nonempty (Model.{u} 𝓣) := by
  constructor
  · intro ⟨𝓜, ρ, h⟩; rw [Vec.eq_nil ρ] at h; exact ⟨⟨𝓜, h⟩⟩
  · intro ⟨𝓜⟩; exists 𝓜, []ᵥ; apply 𝓜.satisfy_theory

end Theory

def Satisfiable.of_model {𝓣 : 𝓛.Theory} (𝓜 : Type u) [𝓛.IsStructure 𝓜] [𝓣.IsModel 𝓜] : Satisfiable.{u} 𝓣 :=
  Theory.satisfiable_iff.mpr ⟨.of 𝓜⟩

def theory (𝓜 : Type u) [𝓛.IsStructure 𝓜] : 𝓛.Theory := { p | 𝓜 ⊨ₛ p }

instance : (𝓛.theory 𝓜).IsModel 𝓜 where
  satisfy_theory _ h := h

theorem theory.satisfiable : Satisfiable.{u} (𝓛.theory 𝓜) := .of_model 𝓜



namespace Structure

def ulift (𝓜 : Structure.{u} 𝓛) : Structure.{max u v} 𝓛 where
  Dom := ULift 𝓜
  interpFunc f v := ULift.up (𝓜.interpFunc f (ULift.down ∘ v))
  interpRel r v := 𝓜.interpRel r (ULift.down ∘ v)

lemma interp_ulift {𝓜 : 𝓛.Structure} {ρ : Vec 𝓜 n} :
  ⟦ t ⟧ₜ 𝓜.ulift, (ULift.up ∘ ρ) = ULift.up (⟦ t ⟧ₜ 𝓜, ρ) := by
  induction t with simp
  | func f v ih => simp [ih]; rfl

lemma satisfy_ulift {𝓜 : 𝓛.Structure} {ρ : Vec 𝓜 n} :
  𝓜.ulift ⊨[ULift.up ∘ ρ] p ↔ 𝓜 ⊨[ρ] p := by
  induction p with simp
  | rel r v => simp [interp_ulift]; rfl
  | eq t₁ t₂ => simp [interp_ulift]; exact ULift.up_inj
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih =>
    constructor
    · intros h u; rw [←ih, Vec.comp_cons]; apply h
    · intros h u; rw [←ULift.up_down u, ←Vec.comp_cons, ih]; apply h

end Structure

theorem Entails.down : Γ ⊨.{max u v} p → Γ ⊨.{u} p := by
  intros h 𝓜 ρ h₁
  have := h 𝓜.ulift (ULift.up ∘ ρ)
  simp [Structure.satisfy_ulift] at this
  exact this h₁

theorem Satisfiable.up : Satisfiable.{u} Γ → Satisfiable.{max u v} Γ := by
  intro ⟨𝓜, ρ, h⟩
  exists 𝓜.ulift, (ULift.up ∘ ρ)
  simp [Structure.satisfy_ulift]
  exact h



namespace Structure

variable {𝓜 𝓝 : 𝓛.Structure}

def ElementaryEquivalent (𝓜 : 𝓛.Structure) (𝓝 : 𝓛.Structure) :=
  ∀ (p : 𝓛.Sentence), 𝓜 ⊨ₛ p ↔ 𝓝 ⊨ₛ p
infixr:25 " ≃ᴱ " => ElementaryEquivalent

theorem ElementaryEquivalent.iff_theory_eq : 𝓜 ≃ᴱ 𝓝 ↔ 𝓛.theory 𝓜 = 𝓛.theory 𝓝 := by
  simp [ElementaryEquivalent, Set.ext_iff, theory]

structure Embedding (𝓜 : 𝓛.Structure) (𝓝 : 𝓛.Structure) extends 𝓜 ↪ 𝓝 where
  on_func {n} : ∀ (f : 𝓛.Func n) (v : Vec 𝓜 n), toEmbedding (IsStructure.interpFunc f v) = IsStructure.interpFunc f (toEmbedding ∘ v)
  on_rel {n} : ∀ (r : 𝓛.Rel n) (v : Vec 𝓜 n), IsStructure.interpRel r v ↔ IsStructure.interpRel r (toEmbedding ∘ v)
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

theorem on_term (e : 𝓜 ↪ᴹ 𝓝) (t : 𝓛.Term n) (ρ : Vec 𝓜 n) : e (⟦t⟧ₜ 𝓜, ρ) = ⟦t⟧ₜ 𝓝, e ∘ ρ := by
  induction t with simp
  | func f v ih => rw [e.on_func]; congr; ext; simp [ih]

def IsElementary (e : 𝓜 ↪ᴹ 𝓝) :=
  ∀ {n} (p : 𝓛.Formula n) (ρ : Vec 𝓜 n), 𝓜 ⊨[ρ] p ↔ 𝓝 ⊨[e ∘ ρ] p

/-- Tarski–Vaught test -/
theorem is_elementary_iff (e : 𝓜 ↪ᴹ 𝓝) :
  e.IsElementary ↔ ∀ {n} (p : 𝓛.Formula (n + 1)) (ρ : Vec 𝓜 n), 𝓝 ⊨[e ∘ ρ] ∃' p → ∃ u, 𝓝 ⊨[e u ∷ᵥ e ∘ ρ] p := by
  constructor
  · intro h n p ρ h₁
    rw [←h] at h₁; simp at h₁
    rcases h₁ with ⟨u, h₁⟩
    exists u
    rw [←Vec.comp_cons, ←h]
    exact h₁
  · intro h n p ρ
    induction p with simp
    | rel r v => rw [e.on_rel]; congr!; simp [e.on_term]
    | eq t₁ t₂ => simp [←e.on_term]
    | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
    | all p ih =>
      constructor
      · intro h₁
        by_contra h₂; simp at h₂
        simp_rw [←satisfy_neg, ←satisfy_ex] at h₂
        apply h at h₂
        rcases h₂ with ⟨u, h₂⟩
        simp [←Vec.comp_cons, ←ih] at h₂
        exact h₂ (h₁ u)
      · intro h₁ u
        rw [ih, Vec.comp_cons]
        apply h₁

end Embedding

structure Isomorphism (𝓜 : 𝓛.Structure) (𝓝 : 𝓛.Structure) extends 𝓜 ≃ 𝓝 where
  on_func {n} : ∀ (f : 𝓛.Func n) (v : Vec 𝓜 n), toEquiv (IsStructure.interpFunc f v) = IsStructure.interpFunc f (toEquiv ∘ v)
  on_rel {n} : ∀ (r : 𝓛.Rel n) (v : Vec 𝓜 n), IsStructure.interpRel r v ↔ IsStructure.interpRel r (toEquiv ∘ v)
infix:25 " ≃ᴹ " => Isomorphism

namespace Isomorphism

instance : CoeFun (𝓜 ≃ᴹ 𝓝) (λ _ => 𝓜 → 𝓝) := ⟨(·.toEquiv)⟩

def refl : 𝓜 ≃ᴹ 𝓜 where
  toEquiv := .refl 𝓜
  on_func f v := rfl
  on_rel r v := by rfl

def symm (i : 𝓜 ≃ᴹ 𝓝) : 𝓝 ≃ᴹ 𝓜 where
  toEquiv := .symm i.toEquiv
  on_func f v := by apply i.toEquiv.injective; simp [i.on_func, Function.comp_def]
  on_rel r v := by rw [i.on_rel]; simp [Function.comp_def]

def trans (i₁ : 𝓜 ≃ᴹ 𝓝) (i₂ : 𝓝 ≃ᴹ 𝓢) : 𝓜 ≃ᴹ 𝓢 where
  toEquiv := .trans i₁.toEquiv i₂.toEquiv
  on_func f v := by simp [i₁.on_func, i₂.on_func]; rfl
  on_rel r v := by rw [i₁.on_rel, i₂.on_rel]; rfl

def toEmbedding (i : 𝓜 ≃ᴹ 𝓝) : 𝓜 ↪ᴹ 𝓝 where
  toEmbedding := i.toEquiv
  on_func := i.on_func
  on_rel := i.on_rel

theorem on_term (i : 𝓜 ≃ᴹ 𝓝) (t : 𝓛.Term n) (ρ : Vec 𝓜 n) : i (⟦t⟧ₜ 𝓜, ρ) = ⟦t⟧ₜ 𝓝, i ∘ ρ := by
  induction t with simp
  | func f v ih => rw [i.on_func]; congr; ext; simp [ih]

theorem on_formula (i : 𝓜 ≃ᴹ 𝓝) (p : 𝓛.Formula n) (ρ : Vec 𝓜 n) : 𝓜 ⊨[ρ] p ↔ 𝓝 ⊨[i ∘ ρ] p := by
  induction p with simp
  | rel r v => rw [i.on_rel]; congr!; simp [i.on_term]
  | eq t₁ t₂ => simp [←i.on_term]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => rw [i.toEquiv.forall_congr]; simp [ih, Vec.comp_cons]

theorem elementary_equivalent (i : 𝓜 ≃ᴹ 𝓝) : 𝓜 ≃ᴱ 𝓝 := by
  intro; simp [i.on_formula, Vec.eq_nil]

end Isomorphism

end Structure

end FirstOrder.Language
