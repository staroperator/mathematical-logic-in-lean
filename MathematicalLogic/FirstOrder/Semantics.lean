import MathematicalLogic.FirstOrder.Syntax

universe u v

namespace FirstOrder.Language

structure Structure (𝓛 : Language) where
  Dom : Type u
  interpFunc : 𝓛.Func n → Vec Dom n → Dom
  interpRel : 𝓛.Rel n → Vec Dom n → Prop

variable {𝓛 : Language} {𝓜 : 𝓛.Structure}

namespace Structure

instance : CoeSort 𝓛.Structure (Type u) := ⟨(·.Dom)⟩

def Assignment (𝓜 : 𝓛.Structure) (n : ℕ) := Vec 𝓜 n

def interpTerm (𝓜 : 𝓛.Structure) : 𝓛.Term n → 𝓜.Assignment n → 𝓜
| #x, ρ => ρ x
| f ⬝ₜ v, ρ => 𝓜.interpFunc f λ i => 𝓜.interpTerm (v i) ρ
notation:80 "⟦" t "⟧ₜ " 𝓜 ", " ρ:80 => interpTerm 𝓜 t ρ

def Assignment.subst (ρ : 𝓜.Assignment n) (σ : 𝓛.Subst m n) : 𝓜.Assignment m :=
  λ x => ⟦ σ x ⟧ₜ 𝓜, ρ
notation:80 ρ "[" σ "]ₐ" => Structure.Assignment.subst ρ σ

lemma Assignment.subst_shift : (u ∷ᵥ ρ)[Subst.shift]ₐ = ρ := by
  funext x; simp [Assignment.subst, interpTerm]

lemma Assignment.subst_single : ρ[↦ₛ t]ₐ = ⟦ t ⟧ₜ 𝓜, ρ ∷ᵥ ρ := by
  funext x; cases x using Fin.cases <;> simp [Assignment.subst, interpTerm]

theorem interpTerm_subst : ⟦ t[σ]ₜ ⟧ₜ 𝓜, ρ = ⟦ t ⟧ₜ 𝓜, ρ[σ]ₐ := by
  induction t with simp [Structure.Assignment.subst, interpTerm]
  | func f v ih => simp [ih]

def interpFormula (𝓜 : 𝓛.Structure) : {n : ℕ} → 𝓛.Formula n → 𝓜.Assignment n → Prop
| _, r ⬝ᵣ v, ρ => 𝓜.interpRel r λ i => ⟦ v i ⟧ₜ 𝓜, ρ
| _, t₁ ≐ t₂, ρ => ⟦ t₁ ⟧ₜ 𝓜, ρ = ⟦ t₂ ⟧ₜ 𝓜, ρ
| _, ⊥, _ => False
| _, p ⇒ q, ρ => 𝓜.interpFormula p ρ → 𝓜.interpFormula q ρ
| _, ∀' p, ρ => ∀ u, 𝓜.interpFormula p (u ∷ᵥ ρ)
notation:50 𝓜 " ⊨[" ρ "] " p:50 => interpFormula 𝓜 p ρ

theorem interp_neg : 𝓜 ⊨[ρ] ~ p ↔ ¬ 𝓜 ⊨[ρ] p := by rfl
theorem interp_or : 𝓜 ⊨[ρ] p ⩒ q ↔ 𝓜 ⊨[ρ] p ∨ 𝓜 ⊨[ρ] q := by simp [interpFormula]; tauto
theorem interp_and : 𝓜 ⊨[ρ] p ⩑ q ↔ 𝓜 ⊨[ρ] p ∧ 𝓜 ⊨[ρ] q := by simp [interpFormula]
theorem interp_iff : 𝓜 ⊨[ρ] p ⇔ q ↔ (𝓜 ⊨[ρ] p ↔ 𝓜 ⊨[ρ] q) := by simp [interpFormula]; tauto
theorem interp_exists : 𝓜 ⊨[ρ] ∃' p ↔ ∃ u, 𝓜 ⊨[u ∷ᵥ ρ] p := by simp [interpFormula]

theorem interp_andN {v : Vec (𝓛.Formula n) m} :
  𝓜 ⊨[ρ] (⋀i, v i) ↔ ∀ i, 𝓜 ⊨[ρ] v i := by
  induction m with simp [Formula.andN]
  | zero => simp [interpFormula]
  | succ n ih => simp [interp_and, ih, Fin.forall_fin_succ, Vec.head]

theorem interpFormula_subst {σ : 𝓛.Subst m n} : 𝓜 ⊨[ρ] p[σ]ₚ ↔ 𝓜 ⊨[ρ[σ]ₐ] p := by
  induction p generalizing n with simp [Assignment.subst, interpFormula]
  | rel | eq => simp [interpTerm_subst]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih =>
      apply forall_congr'
      intro u; simp [ih]; congr!
      funext x; cases x using Fin.cases <;> simp [Assignment.subst, Assignment.subst_shift, interpTerm, Term.shift, interpTerm_subst]

abbrev satisfy (𝓜 : 𝓛.Structure) (p : 𝓛.Sentence) := 𝓜 ⊨[[]ᵥ] p
infix:50 " ⊨ₛ " => satisfy

theorem interp_alls {p : 𝓛.Formula n} : 𝓜 ⊨ₛ ∀* p ↔ ∀ ρ, 𝓜 ⊨[ρ] p := by
  induction n with simp [Formula.alls]
  | zero =>
    constructor
    · intros h _; simp [Vec.eq_nil]; exact h
    · intro h; exact h []ᵥ
  | succ n ih =>
    simp [ih, interpFormula]
    constructor
    · intro h ρ; rw [Vec.eq_cons ρ]; apply h
    · intro h ρ u; exact h (u ∷ᵥ ρ)

end Structure



def Entails (Γ : 𝓛.FormulaSet n) (p) :=
  ∀ (𝓢 : Structure.{u} 𝓛) (ρ), (∀ q ∈ Γ, 𝓢 ⊨[ρ] q) → 𝓢 ⊨[ρ] p

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

structure Model (𝓣 : 𝓛.Theory) extends 𝓛.Structure where
  satisfy_theory : ∀ p ∈ 𝓣, toStructure ⊨ₛ p

variable {𝓣 : 𝓛.Theory}

instance : CoeOut 𝓣.Model 𝓛.Structure := ⟨(·.toStructure)⟩
instance : CoeSort 𝓣.Model (Type u) := ⟨(·.Dom)⟩

theorem entails_iff {𝓣 : 𝓛.Theory} : 𝓣 ⊨.{u} p ↔ ∀ (𝓜 : Model.{u} 𝓣), 𝓜 ⊨ₛ p := by
  constructor
  · intro h 𝓜; apply h; exact 𝓜.satisfy_theory
  · intro h 𝓜 ρ h₁; rw [Vec.eq_nil ρ] at *; exact h ⟨𝓜, h₁⟩

theorem satisfiable_iff {𝓣 : 𝓛.Theory} : Satisfiable.{u} 𝓣 ↔ Nonempty (Model.{u} 𝓣) := by
  constructor
  · intro ⟨𝓜, ρ, h⟩; rw [Vec.eq_nil ρ] at h; exact ⟨⟨𝓜, h⟩⟩
  · intro ⟨𝓜⟩; exists 𝓜, []ᵥ; apply 𝓜.satisfy_theory

end Theory

namespace Structure

def theory (𝓜 : 𝓛.Structure) : 𝓛.Theory :=
  { p | 𝓜 ⊨ₛ p }

theorem theory.satisfiable {𝓜 : Structure.{u} 𝓛} : Satisfiable.{u} 𝓜.theory := by
  rw [Theory.satisfiable_iff]; exact ⟨𝓜, λ _ h => h⟩

end Structure



namespace Structure

def ulift (𝓜 : Structure.{u} 𝓛) : Structure.{max u v} 𝓛 where
  Dom := ULift 𝓜
  interpFunc f v := ULift.up (𝓜.interpFunc f (ULift.down ∘ v))
  interpRel r v := 𝓜.interpRel r (ULift.down ∘ v)

lemma interpTerm_ulift {𝓜 : 𝓛.Structure} {ρ : 𝓜.Assignment n} :
  ⟦ t ⟧ₜ 𝓜.ulift, (ULift.up ∘ ρ) = ULift.up (⟦ t ⟧ₜ 𝓜, ρ) := by
  induction t with simp [interpTerm]
  | func f v ih => simp [ih]; rfl

lemma interpFormula_ulift {𝓜 : 𝓛.Structure} {ρ : 𝓜.Assignment n} :
  𝓜.ulift ⊨[ULift.up ∘ ρ] p ↔ 𝓜 ⊨[ρ] p := by
  induction p with simp [interpFormula]
  | rel r v => simp [interpTerm_ulift]; rfl
  | eq t₁ t₂ => simp [interpTerm_ulift]; exact ULift.up_inj
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih =>
    constructor
    · intros h u; rw [←ih, Vec.comp_cons]; apply h
    · intros h u; rw [←ULift.up_down u, ←Vec.comp_cons, ih]; apply h

end Structure

theorem Entails.down : Γ ⊨.{max u v} p → Γ ⊨.{u} p := by
  intros h 𝓜 ρ h₁
  have := h 𝓜.ulift (ULift.up ∘ ρ)
  simp [Structure.interpFormula_ulift] at this
  exact this h₁

theorem Satisfiable.up : Satisfiable.{u} Γ → Satisfiable.{max u v} Γ := by
  intro ⟨𝓜, ρ, h⟩
  exists 𝓜.ulift, (ULift.up ∘ ρ)
  simp [Structure.interpFormula_ulift]
  exact h



namespace Structure

def ElementaryEquivalent (𝓜 : 𝓛.Structure) (𝓝 : 𝓛.Structure) :=
  ∀ p, 𝓜 ⊨ₛ p ↔ 𝓝 ⊨ₛ p
infixr:25 " ≃ᴱ " => ElementaryEquivalent

theorem ElementaryEquivalent.iff_theory_eq : 𝓜 ≃ᴱ 𝓝 ↔ 𝓜.theory = 𝓝.theory := by
  simp [ElementaryEquivalent, Set.ext_iff, theory]

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
  on_func f v := by simp [Function.comp, e₁.on_func, e₂.on_func]
  on_rel r v := by rw [e₁.on_rel, e₂.on_rel]; simp [Function.comp]

theorem on_term (e : 𝓜 ↪ᴹ 𝓝) (t : 𝓛.Term n) (ρ : 𝓜.Assignment n) : e (⟦t⟧ₜ 𝓜, ρ) = ⟦t⟧ₜ 𝓝, e ∘ ρ := by
  induction t with simp [interpTerm]
  | func f v ih => rw [e.on_func]; congr; ext; simp [ih]

def IsElementary (e : 𝓜 ↪ᴹ 𝓝) :=
  ∀ {n} (p : 𝓛.Formula n) (ρ : 𝓜.Assignment n), 𝓜 ⊨[ρ] p ↔ 𝓝 ⊨[e ∘ ρ] p

/-- Tarski–Vaught test -/
theorem is_elementary_iff (e : 𝓜 ↪ᴹ 𝓝) :
  e.IsElementary ↔ ∀ {n} (p : 𝓛.Formula (n + 1)) (ρ : 𝓜.Assignment n), 𝓝 ⊨[e ∘ ρ] ∃' p → ∃ u, 𝓝 ⊨[e u ∷ᵥ e ∘ ρ] p := by
  constructor
  · intro h n p ρ h₁
    rw [←h] at h₁
    simp [interp_exists] at h₁
    rcases h₁ with ⟨u, h₁⟩
    exists u
    rw [←Vec.comp_cons, ←h]
    exact h₁
  · intro h n p ρ
    induction p with simp [interpFormula]
    | rel r v => rw [e.on_rel]; congr!; simp [e.on_term]
    | eq t₁ t₂ => simp [←e.on_term]
    | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
    | all p ih =>
      constructor
      · intro h₁
        by_contra h₂; simp [←interp_neg, ←interp_exists] at h₂
        apply h at h₂
        rcases h₂ with ⟨u, h₂⟩
        rw [←Vec.comp_cons, interp_neg, ←ih] at h₂
        exact h₂ (h₁ u)
      · intro h₁ u
        rw [ih, Vec.comp_cons]
        apply h₁

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
  on_func f v := by apply i.toEquiv.injective; simp [Function.comp, i.on_func]
  on_rel r v := by rw [i.on_rel]; simp [Function.comp]

def trans (i₁ : 𝓜 ≃ᴹ 𝓝) (i₂ : 𝓝 ≃ᴹ 𝓢) : 𝓜 ≃ᴹ 𝓢 where
  toEquiv := .trans i₁.toEquiv i₂.toEquiv
  on_func f v := by simp [Function.comp, i₁.on_func, i₂.on_func]
  on_rel r v := by rw [i₁.on_rel, i₂.on_rel]; simp [Function.comp]

def toEmbedding (i : 𝓜 ≃ᴹ 𝓝) : 𝓜 ↪ᴹ 𝓝 where
  toEmbedding := i.toEquiv
  on_func := i.on_func
  on_rel := i.on_rel

theorem on_term (i : 𝓜 ≃ᴹ 𝓝) (t : 𝓛.Term n) (ρ : 𝓜.Assignment n) : i (⟦t⟧ₜ 𝓜, ρ) = ⟦t⟧ₜ 𝓝, i ∘ ρ := by
  induction t with simp [interpTerm]
  | func f v ih => rw [i.on_func]; congr; ext; simp [ih]

theorem on_formula (i : 𝓜 ≃ᴹ 𝓝) (p : 𝓛.Formula n) (ρ : 𝓜.Assignment n) : 𝓜 ⊨[ρ] p ↔ 𝓝 ⊨[i ∘ ρ] p := by
  induction p with simp [interpFormula]
  | rel r v => rw [i.on_rel]; congr!; simp [i.on_term]
  | eq t₁ t₂ => simp [←i.on_term]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => rw [i.toEquiv.forall_congr]; simp [ih]

theorem elementary_equivalent (i : 𝓜 ≃ᴹ 𝓝) : 𝓜 ≃ᴱ 𝓝 := by
  intro; simp [i.on_formula]

end Isomorphism

end Structure

end FirstOrder.Language
