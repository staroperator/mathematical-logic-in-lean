import MathematicalLogic.FirstOrder.Syntax

/-!

# Semantics of first-order logic

This file defines the semantics of first-order logic (structures, models, satisfiability, etc.).

-/

namespace FirstOrder.Language

/--
  First-order structures. The name `IsStructure` is to align with `IsModel`, but it's not `Prop`
  valued. Note: structures do not have to be nonempty.
  -/
class IsStructure (L : Language) (M : Type u) where
  interpFunc : L.Func n → Vec M n → M
  interpRel : L.Rel n → Vec M n → Prop

variable {L : Language} {M : Type u} [L.IsStructure M] {t t₁ t₂ : L.Term n} {p q : L.Formula n}

open IsStructure

/-- A term is interpreted by a structures and an assignment of type `Vec M n`. -/
def interp (M : Type u) [L.IsStructure M] : L.Term n → Vec M n → M
| #x, ρ => ρ x
| f ⬝ᶠ v, ρ => interpFunc f λ i => interp M (v i) ρ
notation:80 "⟦" t "⟧ₜ " α ", " ρ:80 => interp α t ρ

@[simp] theorem interp_var : ⟦ (#x : L.Term n) ⟧ₜ M, ρ = ρ x := rfl
@[simp] theorem interp_func : ⟦ (f ⬝ᶠ v : L.Term n) ⟧ₜ M, ρ = interpFunc f λ i => ⟦ v i ⟧ₜ M, ρ := rfl

theorem interp_subst : ⟦ t[σ]ₜ ⟧ₜ M, ρ = ⟦ t ⟧ₜ M, λ x => ⟦ σ x ⟧ₜ M, ρ := by
  induction t with simp
  | func f v ih => simp [ih]

theorem interp_shift : ⟦ ↑ₜt ⟧ₜ M, (u ∷ᵥ ρ) = ⟦ t ⟧ₜ M, ρ := by
  simp [Term.shift, interp_subst]

/-- A formula is satisfied by a structure and an assignment if it is interpreted as true. -/
def satisfy (M : Type u) [L.IsStructure M] : {n : ℕ} → L.Formula n → Vec M n → Prop
| _, r ⬝ʳ v, ρ => interpRel r λ i => ⟦ v i ⟧ₜ M, ρ
| _, t₁ ≐ t₂, ρ => ⟦ t₁ ⟧ₜ M, ρ = ⟦ t₂ ⟧ₜ M, ρ
| _, ⊥, _ => False
| _, p ⇒ q, ρ => satisfy M p ρ → satisfy M q ρ
| _, ∀' p, ρ => ∀ u, satisfy M p (u ∷ᵥ ρ)
notation:50 M " ⊨[" ρ "] " p:50 => satisfy M p ρ

@[simp] theorem satisfy_rel : M ⊨[ρ] (r ⬝ʳ v : L.Formula n) ↔ interpRel r λ i => ⟦ v i ⟧ₜ M, ρ := by rfl
@[simp] theorem satisfy_eq : M ⊨[ρ] t₁ ≐ t₂ ↔ ⟦ t₁ ⟧ₜ M, ρ = ⟦ t₂ ⟧ₜ M, ρ := by rfl
@[simp] theorem satisfy_false : ¬ M ⊨[ρ] (⊥ : L.Formula n) := by tauto
@[simp] theorem satisfy_imp : M ⊨[ρ] p ⇒ q ↔ M ⊨[ρ] p → M ⊨[ρ] q := by rfl
@[simp] theorem satisfy_true : M ⊨[ρ] (⊤ : L.Formula n) := by tauto
@[simp] theorem satisfy_neg : M ⊨[ρ] ~ p ↔ ¬ M ⊨[ρ] p := by rfl
@[simp] theorem satisfy_and : M ⊨[ρ] p ⩑ q ↔ M ⊨[ρ] p ∧ M ⊨[ρ] q := by simp [PropNotation.and]
@[simp] theorem satisfy_or : M ⊨[ρ] p ⩒ q ↔ M ⊨[ρ] p ∨ M ⊨[ρ] q := by simp [PropNotation.or]; tauto
@[simp] theorem satisfy_iff : M ⊨[ρ] p ⇔ q ↔ (M ⊨[ρ] p ↔ M ⊨[ρ] q) := by simp [PropNotation.iff]; tauto
@[simp] theorem satisfy_all {p : L.Formula (n + 1)} : M ⊨[ρ] ∀' p ↔ ∀ u, M ⊨[u ∷ᵥ ρ] p := by rfl
@[simp] theorem satisfy_ex {p : L.Formula (n + 1)} : M ⊨[ρ] ∃' p ↔ ∃ u, M ⊨[u ∷ᵥ ρ] p := by simp [Formula.ex]

theorem satisfy_andN {v : Vec (L.Formula n) m} :
  M ⊨[ρ] (⋀ i, v i) ↔ ∀ i, M ⊨[ρ] v i := by
  induction m with simp [Formula.andN]
  | succ n ih => simp [Vec.head, ih, Fin.forall_fin_succ]

theorem satisfy_orN {v : Vec (L.Formula n) m} :
  M ⊨[ρ] (⋁ i, v i) ↔ ∃ i, M ⊨[ρ] v i := by
  induction m with simp [Formula.orN]
  | succ n ih => simp [Vec.head, ih, Fin.exists_fin_succ]

theorem satisfy_allN {p : L.Formula (n + m)} :
  M ⊨[ρ] ∀^[m] p ↔ ∀ v, M ⊨[v ++ᵥ ρ] p := by
  induction m with simp [Formula.allN, Vec.eq_nil]
  | succ m ih =>
    rw [ih]; simp [Fin.forall_fin_succ_pi]; rw [forall_comm]; rfl

theorem satisfy_exN {p : L.Formula (n + m)} :
  M ⊨[ρ] ∃^[m] p ↔ ∃ v, M ⊨[v ++ᵥ ρ] p := by
  induction m with simp [Formula.exN, Vec.eq_nil]
  | succ m ih =>
    rw [ih]; simp [Fin.exists_fin_succ_pi]; rw [exists_comm]; rfl

theorem satisfy_subst {σ : L.Subst n m} :
  M ⊨[ρ] p[σ]ₚ ↔ M ⊨[λ x => ⟦ σ x ⟧ₜ M, ρ] p := by
  induction p generalizing m with simp
  | rel | eq => simp [interp_subst]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih =>
    apply forall_congr'
    intro u; simp [ih]
    congr! with x
    cases x using Fin.cases <;> simp [interp_shift]

theorem satisfy_subst_single {p : L.Formula (n + 1)} :
  M ⊨[ρ] p[↦ₛ t]ₚ ↔ M ⊨[ ⟦t⟧ₜ M, ρ ∷ᵥ ρ ] p := by
  simp [satisfy_subst]
  congr! with x
  cases x using Fin.cases <;> simp

theorem satisfy_subst_assign {p : L.Formula (n + 1)} {t} :
  M ⊨[ρ] p[≔ₛ t]ₚ ↔ M ⊨[ ⟦t⟧ₜ M, ρ ∷ᵥ ρ.tail ] p := by
  simp [satisfy_subst]
  congr! with x
  cases x using Fin.cases <;> simp

theorem satisfy_shift : M ⊨[u ∷ᵥ ρ] ↑ₚp ↔ M ⊨[ρ] p := by
  simp [Formula.shift, satisfy_subst]

abbrev satisfys (M : Type u) [L.IsStructure M] (p : L.Sentence) := M ⊨[[]ᵥ] p
infix:50 " ⊨ₛ " => satisfys

theorem satisfy_alls : M ⊨ₛ ∀* p ↔ ∀ ρ, M ⊨[ρ] p := by
  induction n with simp [Formula.alls]
  | zero => rfl
  | succ n ih =>
    simp [ih]
    constructor
    · intro h ρ; rw [Vec.eq_cons ρ]; apply h
    · intro h ρ u; exact h (u ∷ᵥ ρ)

/-- Bundled version of `IsStructure`. -/
structure Structure (L : Language) where
  Dom : Type u
  interpFunc {n} : L.Func n → Vec Dom n → Dom
  interpRel {n} : L.Rel n → Vec Dom n → Prop

namespace Structure

instance : CoeSort L.Structure (Type u) := ⟨(·.Dom)⟩
instance {M : L.Structure} : L.IsStructure M := ⟨M.interpFunc, M.interpRel⟩
@[reducible] def of (M : Type u) [L.IsStructure M] : L.Structure := ⟨M, IsStructure.interpFunc, IsStructure.interpRel⟩

end Structure

/-- `Γ ⊨ p` (called `Γ` entails `p`) if any structure that satisfies `Γ` must also satisfy `p`. -/
def Entails (Γ : L.FormulaSet n) (p : L.Formula n) :=
  ∀ (M : Structure.{u} L) (ρ), (∀ q ∈ Γ, M ⊨[ρ] q) → M ⊨[ρ] p

infix:50 " ⊨ " => Entails
syntax:50 term " ⊨.{" level "} " term:50 : term
macro_rules
| `($Γ ⊨.{$u} $p) => `(Entails.{$u} $Γ $p)

/--
  `Γ` is satisfiable if there is a structure and an assignment that satisfy all formulas in `Γ`.
  The assignment is not needed for `Theory` (see `Theory.satisfiable_iff`).
  -/
def Satisfiable (Γ : L.FormulaSet n) :=
  ∃ (𝓢 : Structure.{u} L), ∃ ρ, ∀ p ∈ Γ, 𝓢 ⊨[ρ] p

theorem Satisfiable.weaken :
  Γ ⊆ Δ → Satisfiable.{u} Δ → Satisfiable.{u} Γ := by
  rintro h₁ ⟨𝓢, ⟨ρ, h₂⟩⟩
  exists 𝓢, ρ
  intros p h₃
  apply h₂
  apply h₁
  exact h₃

theorem Satisfiable.empty : Satisfiable (∅ : L.FormulaSet n) := by
  exists ⟨PUnit, λ _ v => .unit, λ _ _ => True⟩, λ _ => .unit
  simp

namespace Theory

/-- A structure `M` is a model of theory `T` if it satisfies all the axioms of `T`. -/
class IsModel (T : L.Theory) (M : Type u) [L.IsStructure M] : Prop where
  satisfy_theory : ∀ p ∈ T, M ⊨ₛ p

/-- Bundled version of `IsModel`. -/
structure Model (T : L.Theory) extends L.Structure where
  satisfy_theory : ∀ p ∈ T, toStructure ⊨ₛ p

variable {T : L.Theory} {M : T.Model} {p q : L.Sentence}

namespace Model

instance : CoeOut T.Model L.Structure := ⟨(·.toStructure)⟩
instance : CoeSort T.Model (Type u) := ⟨(·.Dom)⟩
instance : T.IsModel M := ⟨M.satisfy_theory⟩

@[reducible] def of (M : Type u) [L.IsStructure M] [T.IsModel M] : T.Model := ⟨Structure.of M, IsModel.satisfy_theory⟩

end Model

theorem entails_iff : T ⊨.{u} p ↔ ∀ (M : Model.{u} T), M ⊨ₛ p := by
  constructor
  · intro h M; apply h; exact M.satisfy_theory
  · intro h M ρ h₁; rw [Vec.eq_nil ρ] at *; exact h ⟨M, h₁⟩

theorem satisfiable_iff : Satisfiable.{u} T ↔ Nonempty (Model.{u} T) := by
  constructor
  · intro ⟨M, ρ, h⟩; rw [Vec.eq_nil ρ] at h; exact ⟨⟨M, h⟩⟩
  · intro ⟨M⟩; exists M, []ᵥ; apply M.satisfy_theory

end Theory

def Satisfiable.of_model {T : L.Theory} (M : Type u) [L.IsStructure M] [T.IsModel M] : Satisfiable.{u} T :=
  Theory.satisfiable_iff.mpr ⟨.of M⟩

/-- The theory of a structure `M` contains all sentences satisfied by `M` as axioms. -/
def theory (L : Language) (M : Type u) [L.IsStructure M] : L.Theory := { p | M ⊨ₛ p }

instance : (L.theory M).IsModel M where
  satisfy_theory _ h := h

theorem theory.satisfiable : Satisfiable.{u} (L.theory M) := .of_model M

namespace Structure

def ulift (M : Structure.{u} L) : Structure.{max u v} L where
  Dom := ULift M
  interpFunc f v := ULift.up (M.interpFunc f (ULift.down ∘ v))
  interpRel r v := M.interpRel r (ULift.down ∘ v)

lemma interp_ulift {M : L.Structure} {ρ : Vec M n} :
  ⟦ t ⟧ₜ M.ulift, (ULift.up ∘ ρ) = ULift.up (⟦ t ⟧ₜ M, ρ) := by
  induction t with simp
  | func f v ih => simp [ih]; rfl

lemma satisfy_ulift {M : L.Structure} {ρ : Vec M n} :
  M.ulift ⊨[ULift.up ∘ ρ] p ↔ M ⊨[ρ] p := by
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
  intros h M ρ h₁
  have := h M.ulift (ULift.up ∘ ρ)
  simp [Structure.satisfy_ulift] at this
  exact this h₁

theorem Satisfiable.up : Satisfiable.{u} Γ → Satisfiable.{max u v} Γ := by
  intro ⟨M, ρ, h⟩
  exists M.ulift, (ULift.up ∘ ρ)
  simp [Structure.satisfy_ulift]
  exact h

namespace Structure

variable {M N : L.Structure}

/-- Two structures are elementary equivalent if they satisfy the same sentences. -/
def ElementaryEquivalent (M : L.Structure) (N : L.Structure) :=
  ∀ (p : L.Sentence), M ⊨ₛ p ↔ N ⊨ₛ p
infixr:25 " ≃ᴱ " => ElementaryEquivalent

theorem ElementaryEquivalent.iff_theory_eq : M ≃ᴱ N ↔ L.theory M = L.theory N := by
  simp [ElementaryEquivalent, Set.ext_iff, theory]

structure Embedding (M : L.Structure) (N : L.Structure) extends M ↪ N where
  on_func {n} : ∀ (f : L.Func n) (v : Vec M n), toEmbedding (IsStructure.interpFunc f v) = IsStructure.interpFunc f (toEmbedding ∘ v)
  on_rel {n} : ∀ (r : L.Rel n) (v : Vec M n), IsStructure.interpRel r v ↔ IsStructure.interpRel r (toEmbedding ∘ v)
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

theorem on_term (e : M ↪ᴹ N) (t : L.Term n) (ρ : Vec M n) : e (⟦t⟧ₜ M, ρ) = ⟦t⟧ₜ N, e ∘ ρ := by
  induction t with simp
  | func f v ih => rw [e.on_func]; congr; ext; simp [ih]

def IsElementary (e : M ↪ᴹ N) :=
  ∀ {n} (p : L.Formula n) (ρ : Vec M n), M ⊨[ρ] p ↔ N ⊨[e ∘ ρ] p

/-- Tarski–Vaught test. -/
theorem is_elementary_iff (e : M ↪ᴹ N) :
  e.IsElementary ↔ ∀ {n} (p : L.Formula (n + 1)) (ρ : Vec M n), N ⊨[e ∘ ρ] ∃' p → ∃ u, N ⊨[e u ∷ᵥ e ∘ ρ] p := by
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

structure Isomorphism (M : L.Structure) (N : L.Structure) extends M ≃ N where
  on_func {n} : ∀ (f : L.Func n) (v : Vec M n), toEquiv (IsStructure.interpFunc f v) = IsStructure.interpFunc f (toEquiv ∘ v)
  on_rel {n} : ∀ (r : L.Rel n) (v : Vec M n), IsStructure.interpRel r v ↔ IsStructure.interpRel r (toEquiv ∘ v)
infix:25 " ≃ᴹ " => Isomorphism

namespace Isomorphism

instance : CoeFun (M ≃ᴹ N) (λ _ => M → N) := ⟨(·.toEquiv)⟩

def refl : M ≃ᴹ M where
  toEquiv := .refl M
  on_func f v := rfl
  on_rel r v := by rfl

def symm (i : M ≃ᴹ N) : N ≃ᴹ M where
  toEquiv := .symm i.toEquiv
  on_func f v := by apply i.toEquiv.injective; simp [i.on_func, Function.comp_def]
  on_rel r v := by rw [i.on_rel]; simp [Function.comp_def]

def trans (i₁ : M ≃ᴹ N) (i₂ : N ≃ᴹ 𝓢) : M ≃ᴹ 𝓢 where
  toEquiv := .trans i₁.toEquiv i₂.toEquiv
  on_func f v := by simp [i₁.on_func, i₂.on_func]; rfl
  on_rel r v := by rw [i₁.on_rel, i₂.on_rel]; rfl

def toEmbedding (i : M ≃ᴹ N) : M ↪ᴹ N where
  toEmbedding := i.toEquiv
  on_func := i.on_func
  on_rel := i.on_rel

theorem on_term (i : M ≃ᴹ N) (t : L.Term n) (ρ : Vec M n) : i (⟦t⟧ₜ M, ρ) = ⟦t⟧ₜ N, i ∘ ρ := by
  induction t with simp
  | func f v ih => rw [i.on_func]; congr; ext; simp [ih]

theorem on_formula (i : M ≃ᴹ N) (p : L.Formula n) (ρ : Vec M n) : M ⊨[ρ] p ↔ N ⊨[i ∘ ρ] p := by
  induction p with simp
  | rel r v => rw [i.on_rel]; congr!; simp [i.on_term]
  | eq t₁ t₂ => simp [←i.on_term]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => rw [i.toEquiv.forall_congr]; simp [ih, Vec.comp_cons]

theorem elementary_equivalent (i : M ≃ᴹ N) : M ≃ᴱ N := by
  intro; simp [i.on_formula, Vec.eq_nil]

end Isomorphism

end Structure

end FirstOrder.Language
