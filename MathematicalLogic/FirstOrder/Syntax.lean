import MathematicalLogic.Vector
import MathematicalLogic.Notation
import Mathlib.Data.Set.Lattice

namespace FirstOrder

structure Language where
  𝓕 : ℕ → Type
  [decEq𝓕 : ∀ {n}, DecidableEq (𝓕 n)]
  𝓡 : ℕ → Type
  [decEq𝓡 : ∀ {n}, DecidableEq (𝓡 n)]

namespace Language

variable {𝓛 : Language}

abbrev Const := 𝓛.𝓕 0
instance : DecidableEq (𝓛.𝓕 n) := 𝓛.decEq𝓕
instance : DecidableEq (𝓛.𝓡 n) := 𝓛.decEq𝓡

inductive Term (𝓛 : Language) : Type where
| var : ℕ → 𝓛.Term
| func : 𝓛.𝓕 n → (Fin n → 𝓛.Term) → 𝓛.Term
prefix:max "#" => Term.var
infix:70 " ⬝ₜ " => Term.func
instance : Coe 𝓛.Const 𝓛.Term := ⟨λ c => c ⬝ₜ []ᵥ⟩

instance Term.decEq : DecidableEq 𝓛.Term := by
  intro t₁ t₂
  cases t₁ <;> cases t₂
  case var.var => rw [Term.var.injEq]; apply Nat.decEq
  case func.func n f v₁ m g v₂ =>
    by_cases h : n = m
    · subst h; simp [Term.func.injEq]; rw [←Vec.ext_iff]
      have := λ i => decEq (v₁ i) (v₂ i)
      apply And.decidable
    · simp [h]; exact isFalse not_false
  all_goals exact isFalse Term.noConfusion

def Term.vars : 𝓛.Term → Set ℕ
| #x => {x}
| _ ⬝ₜ v => ⋃ i, (v i).vars

def Subst (𝓛 : Language) := ℕ → 𝓛.Term

def Term.subst : 𝓛.Term → 𝓛.Subst → 𝓛.Term
| #x, σ => σ x
| f ⬝ₜ v, σ => f ⬝ₜ λ i => (v i).subst σ
notation:80 t "[" σ "]ₜ" => Term.subst t σ
@[simp] theorem Term.subst_var : (#x)[σ]ₜ = σ x := rfl
@[simp] theorem Term.subst_func : (f ⬝ₜ v)[σ]ₜ = f ⬝ₜ λ i => (v i)[σ]ₜ := rfl

def Subst.id : 𝓛.Subst := (#·)
@[simp] theorem Subst.id_app : (id x : 𝓛.Term) = #x := rfl
@[simp] theorem Term.subst_id : t[Subst.id]ₜ = t := by
  induction t with simp
  | func f v ih => ext; apply ih

def Subst.comp (σ₁ σ₂ : 𝓛.Subst) : 𝓛.Subst := λ x => (σ₁ x)[σ₂]ₜ
infixl:90 " ∘ₛ " => Subst.comp
@[simp] theorem Subst.comp_app : (σ₁ ∘ₛ σ₂) x = (σ₁ x)[σ₂]ₜ := rfl
@[simp] theorem Term.subst_comp : t[σ₁ ∘ₛ σ₂]ₜ = t[σ₁]ₜ[σ₂]ₜ := by
  induction t with simp
  | func f v ih => ext; apply ih

def Subst.cons (t : 𝓛.Term) (σ : 𝓛.Subst) : 𝓛.Subst
| 0 => t
| x + 1 => σ x
infixl:90 " ∷ₛ " => Subst.cons
@[simp] theorem Subst.cons_app_zero : (t ∷ₛ σ) 0 = t := rfl
@[simp] theorem Subst.cons_app_succ : (t ∷ₛ σ) (x + 1) = σ x := rfl

def Subst.single (t : 𝓛.Term) : 𝓛.Subst := t ∷ₛ id
prefix:max "↦ₛ " => Subst.single
@[simp] theorem Subst.single_app_zero : (↦ₛ t) 0 = t := rfl
@[simp] theorem Subst.single_app_succ : (↦ₛ t) (x + 1) = #x := rfl

def Subst.shift : 𝓛.Subst := λ x => #(x + 1)
def Term.shift (t : 𝓛.Term) := t[Subst.shift]ₜ
prefix:max "↑ₜ" => Term.shift
@[simp] theorem Subst.shift_app : (shift x : 𝓛.Term) = #(x + 1) := rfl
@[simp] theorem Term.shift_var : ↑ₜ(#x : 𝓛.Term) = #(x + 1) := rfl

theorem Term.shift_subst_cons : (↑ₜt₁)[t₂ ∷ₛ σ]ₜ = t₁[σ]ₜ := by
  rw [shift, ←subst_comp]; rfl
theorem Term.shift_subst_single : (↑ₜt₁)[↦ₛ t₂]ₜ = t₁ := by
  simp [Subst.single]; rw [shift_subst_cons, subst_id]

def Subst.assign (t : 𝓛.Term) : 𝓛.Subst := t ∷ₛ shift
prefix:max "≔ₛ " => Subst.assign
@[simp] theorem Subst.assign_app_zero : (≔ₛ t) 0 = t := rfl
@[simp] theorem Subst.assign_app_succ : (≔ₛ t) (x + 1) = #(x + 1) := rfl

def Subst.lift (σ : 𝓛.Subst) : 𝓛.Subst
| 0 => #0
| x + 1 => ↑ₜ(σ x)
prefix:max "⇑ₛ" => Subst.lift
@[simp] theorem Subst.lift_app_zero : ⇑ₛσ 0 = #0 := rfl
@[simp] theorem Subst.lift_app_succ : ⇑ₛσ (x + 1) = ↑ₜ(σ x) := rfl
theorem Term.shift_subst_lift : (↑ₜt)[⇑ₛσ]ₜ = ↑ₜ(t[σ]ₜ) := by
  simp_rw [shift, ←subst_comp]; congr
theorem Subst.lift_id : ⇑ₛ(@id 𝓛) = id := by
  funext x; cases x <;> simp
theorem Subst.lift_comp : ⇑ₛ(σ₁ ∘ₛ σ₂) = ⇑ₛσ₁ ∘ₛ ⇑ₛσ₂ := by
  funext x; cases x <;> simp [Term.shift_subst_lift]

theorem Term.subst_ext_vars {t : 𝓛.Term} (h : ∀ x ∈ t.vars, σ₁ x = σ₂ x) :
  t[σ₁]ₜ = t[σ₂]ₜ := by
  induction t with simp [h, vars]
  | func t v ih => ext i; apply ih; intros; apply h; simp [vars]; exists i

theorem Term.vars_of_subst : t[σ]ₜ.vars = ⋃ x ∈ t.vars, (σ x).vars := by
  induction t with simp [vars]
  | func t v ih => rw [Set.iUnion_comm]; simp_rw [ih]

theorem Term.is_shift_iff : (∃ t', t = ↑ₜt') ↔ 0 ∉ t.vars := by
  constructor
  · rintro ⟨t, h⟩; subst h
    intro h; simp [shift, vars_of_subst] at h
    rcases h with ⟨x, ⟨_, h⟩⟩
    contradiction
  · intro h
    exists t[↦ₛ #0]ₜ
    rw [shift, ←subst_comp]
    conv => lhs; rw [←subst_id (t := t)]
    apply subst_ext_vars
    intros x h₁
    cases x
    · contradiction
    · rfl

theorem Term.subst_swap : t[↦ₛ t₁]ₜ[σ]ₜ = t[⇑ₛσ]ₜ[↦ₛ (t₁[σ]ₜ)]ₜ := by
  simp_rw [←subst_comp]
  congr; funext i
  cases i <;> simp [shift_subst_single]



inductive Formula (𝓛 : Language) : Type where
| rel : 𝓛.𝓡 n → (Fin n → 𝓛.Term) → 𝓛.Formula
| eq : 𝓛.Term → 𝓛.Term → 𝓛.Formula
| false : 𝓛.Formula
| imp : 𝓛.Formula → 𝓛.Formula → 𝓛.Formula
| all : 𝓛.Formula → 𝓛.Formula
infix:70 " ⬝ᵣ " => Formula.rel
instance : PropNotation 𝓛.Formula := ⟨Formula.false, Formula.imp⟩
prefix:59 "∀' " => Formula.all
abbrev Formula.exist (p : 𝓛.Formula) := ~ ∀' (~ p)
prefix:59 "∃' " => Formula.exist

def Formula.andN : {n : ℕ} → Vec 𝓛.Formula n → 𝓛.Formula
| 0, _ => ⊤
| _ + 1, v => v.head ⩑ andN v.tail
notation3:57 "⋀"(...)", " r:(scoped r => Formula.andN r) => r

infix:60 (priority := high) " ≐ " => Formula.eq

@[simp] theorem Formula.false_eq : Formula.false = (⊥ : 𝓛.Formula) := rfl
@[simp] theorem Formula.imp_eq : Formula.imp p q = p ⇒ q := rfl

instance Formula.decEq : DecidableEq 𝓛.Formula := by
  intro p q
  cases p <;> cases q
  case rel.rel n r₁ v₁ m r₂ v₂ =>
    by_cases h : n = m
    · subst h; simp [Formula.rel.injEq]; rw [←Vec.ext_iff]
      apply And.decidable
    · simp [h]; exact isFalse not_false
  case eq.eq =>
    rw [Formula.eq.injEq]; apply And.decidable
  case false.false => exact isTrue rfl
  case imp.imp p₁ q₁ p₂ q₂ =>
    rw [Formula.imp.injEq]
    have := decEq p₁ p₂
    have := decEq q₁ q₂
    apply And.decidable
  case all.all p q =>
    rw [Formula.all.injEq]
    exact decEq p q
  all_goals exact isFalse Formula.noConfusion

def Formula.free : 𝓛.Formula → Set ℕ
| _ ⬝ᵣ ts => ⋃ i, (ts i).vars
| t₁ ≐ t₂ => t₁.vars ∪ t₂.vars
| ⊥ => {}
| p ⇒ q => p.free ∪ q.free
| ∀' p => { x | x + 1 ∈ p.free }

def Formula.subst : 𝓛.Formula → 𝓛.Subst → 𝓛.Formula
| r ⬝ᵣ ts, σ => r ⬝ᵣ (λ i => (ts i).subst σ)
| t₁ ≐ t₂, σ => t₁.subst σ ≐ t₂.subst σ
| ⊥, _ => ⊥
| p ⇒ q, σ => p.subst σ ⇒ q.subst σ
| ∀' p, σ => ∀' (p.subst ⇑ₛσ)
notation:80 p "[" σ "]ₚ" => Formula.subst p σ
@[simp] theorem Formula.subst_rel : (r ⬝ᵣ ts)[σ]ₚ = r ⬝ᵣ (λ i => (ts i)[σ]ₜ) := rfl
@[simp] theorem Formula.subst_eq : (t₁ ≐ t₂)[σ]ₚ = t₁[σ]ₜ ≐ t₂[σ]ₜ := rfl
@[simp] theorem Formula.subst_false : ⊥[σ]ₚ = ⊥ := rfl
@[simp] theorem Formula.subst_imp : (p ⇒ q)[σ]ₚ = p[σ]ₚ ⇒ q[σ]ₚ := rfl
@[simp] theorem Formula.subst_all : (∀' p)[σ]ₚ = ∀' (p[⇑ₛσ]ₚ) := rfl
@[simp] theorem Formula.subst_neg : (~ p)[σ]ₚ = ~ p[σ]ₚ := rfl

def Formula.shift : 𝓛.Formula → 𝓛.Formula := λ p => p[Subst.shift]ₚ
prefix:max "↑ₚ" => Formula.shift

abbrev Formula.existUnique (p : 𝓛.Formula) :=
  ∃' (p ⩑ ∀' ((↑ₚp)[≔ₛ #0]ₚ ⇒ #0 ≐ #1))
prefix:59 "∃!' " => Formula.existUnique

theorem Formula.subst_id : p[Subst.id]ₚ = p := by
  induction p with simp
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => simp [Subst.lift_id, ih]

theorem Formula.subst_comp : p[σ₁ ∘ₛ σ₂]ₚ = p[σ₁]ₚ[σ₂]ₚ := by
  induction p generalizing σ₁ σ₂ with simp
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => simp [Subst.lift_comp, ih]

theorem Formula.shift_subst_single : (↑ₚp)[↦ₛ t₂]ₚ = p := by
  rw [shift, ←subst_comp]
  conv => rhs; rw [←subst_id (p := p)]

theorem Formula.shift_subst_lift : (↑ₚp)[⇑ₛσ]ₚ = ↑ₚ(p[σ]ₚ) := by
  simp_rw [shift, ←subst_comp]; congr

theorem Formula.subst_ext_free {p : 𝓛.Formula} :
  (∀ x ∈ p.free, σ₁ x = σ₂ x) → p[σ₁]ₚ = p[σ₂]ₚ := by
  intro h
  induction p generalizing σ₁ σ₂ with simp
  | rel =>
    ext i; apply Term.subst_ext_vars
    intros; apply h; simp [free]
    exists i
  | eq =>
    constructor <;> apply Term.subst_ext_vars
      <;> intros _ h₁ <;> apply h <;> simp [free, h₁]
  | imp p q ih₁ ih₂ =>
    congr 1 <;> apply_assumption
      <;> intros _ h₁ <;> apply h <;> simp [free, h₁]
  | all _ ih =>
    apply ih; intro x h₁; cases x <;> simp
    · congr; apply h; simp [free]; exact h₁

theorem Formula.free_of_subst :
  p[σ]ₚ.free = ⋃ x ∈ p.free, (σ x).vars := by
  induction p generalizing σ with simp_rw [Formula.free]
  | rel => simp [Term.vars_of_subst]; rw [Set.iUnion_comm]
  | eq => simp [Set.iUnion_or, Set.iUnion_union_distrib, Term.vars_of_subst]
  | false => simp
  | imp p q ih₁ ih₂ => rw [ih₁, ih₂, Set.biUnion_union]
  | all p ih =>
    ext x; simp [ih]
    constructor
    · rintro ⟨y, h₁, h₂⟩
      cases y with
      | zero => contradiction
      | succ y =>
        simp [Subst.lift, Term.shift, Term.vars_of_subst] at h₂
        rcases h₂ with ⟨z, h₂, h₃⟩
        simp [Subst.shift, Term.vars] at h₃
        subst h₃
        exists y
    · rintro ⟨y, ⟨h₁, h₂⟩⟩
      exists y + 1
      constructor
      · exact h₁
      · simp [Subst.lift, Term.shift, Term.vars_of_subst]
        exists x

theorem Formula.is_shift_iff : (∃ p', p = ↑ₚp') ↔ 0 ∉ p.free := by
  constructor
  · rintro ⟨p', h⟩
    subst h
    intro h
    simp [shift, free_of_subst] at h
    rcases h with ⟨x, ⟨_, h⟩⟩
    contradiction
  · intro h
    exists p[↦ₛ #0]ₚ
    rw [shift, ←subst_comp]
    conv => lhs; rw [←subst_id (p := p)]
    apply subst_ext_free
    intros x h₁
    cases x
    · contradiction
    · rfl

theorem Formula.subst_swap : p[↦ₛ t]ₚ[σ]ₚ = p[⇑ₛσ]ₚ[↦ₛ (t[σ]ₜ)]ₚ := by
  simp_rw [←subst_comp]
  congr; funext i
  cases i <;> simp [Term.shift_subst_single]



inductive BTerm (𝓛 : Language) : ℕ → Type where
| var : Fin n → 𝓛.BTerm n
| func : 𝓛.𝓕 m → (Fin m → 𝓛.BTerm n) → 𝓛.BTerm n
prefix:max "#ᵇ" => BTerm.var
infix:70 " ⬝ₜᵇ " => BTerm.func
instance : Coe 𝓛.Const (𝓛.BTerm n) := ⟨λ c => c ⬝ₜᵇ []ᵥ⟩

def BTerm.val : 𝓛.BTerm m → 𝓛.Term
| #ᵇx => #x
| f ⬝ₜᵇ v => f ⬝ₜ λ i => (v i).val
@[simp] theorem BTerm.val_var : (#ᵇx : 𝓛.BTerm m).val = #x := rfl
@[simp] theorem BTerm.val_func : (f ⬝ₜᵇ v).val = f ⬝ₜ λ i => (v i).val := rfl

@[simp] def Term.bound : 𝓛.Term → ℕ
| #x => x + 1
| _ ⬝ₜ v => Vec.max (λ i => (v i).bound)

theorem BTerm.property : (t : 𝓛.BTerm m).val.bound ≤ m := by
  induction t with simp
  | var x => exact x.isLt
  | func f v ih => apply Vec.max_le; intro; apply ih

def BTerm.mk :
  (t : 𝓛.Term) → m ≥ t.bound → 𝓛.BTerm m
| #x, h => #ᵇ⟨x, by simp at h; exact h⟩
| f ⬝ₜ v, h => f ⬝ₜᵇ (λ i => mk (v i) (Nat.le_trans (Vec.le_max (v := Term.bound ∘ v)) h))

theorem BTerm.val_mk {t : 𝓛.Term} {h : m ≥ t.bound} :
  (mk t h).val = t := by
  induction t with simp [mk]
  | func f ts ih => ext; simp [ih]

def BSubst (𝓛 : Language) (n m) := Vec (𝓛.BTerm m) n

def BTerm.subst : 𝓛.BTerm n → 𝓛.BSubst n m → 𝓛.BTerm m
| #ᵇ x, σ => σ x
| f ⬝ₜᵇ v, σ => f ⬝ₜᵇ (λ i => (v i).subst σ)
notation:80 t "[" σ "]ₜᵇ" => BTerm.subst t σ

@[simp] theorem BTerm.subst_var : (#ᵇx)[σ]ₜᵇ = σ x := rfl
@[simp] theorem BTerm.subst_func : (f ⬝ₜᵇ v)[σ]ₜᵇ = f ⬝ₜᵇ (λ i => (v i)[σ]ₜᵇ) := rfl

def BSubst.id : 𝓛.BSubst n n := λ i => #ᵇ i
@[simp] theorem BSubst.id_app : (id x : 𝓛.BTerm n) = #ᵇx := rfl
@[simp] theorem BTerm.subst_id : t[BSubst.id]ₜᵇ = t := by
  induction t with simp
  | func f v ih => ext; apply ih

def BSubst.single (t : 𝓛.BTerm m) : 𝓛.BSubst (m + 1) m :=
  t ∷ᵥ id
prefix:max "↦ᵇ " => BSubst.single
@[simp] theorem BSubst.single_app_zero : (↦ᵇ t) 0 = t := rfl
@[simp] theorem BSubst.single_app_succ : (↦ᵇ t) x.succ = #ᵇx := rfl

def BSubst.shift : 𝓛.BSubst m (m + 1) := λ x => #ᵇ(Fin.succ x)
def BTerm.shift (t : 𝓛.BTerm m) := t[BSubst.shift]ₜᵇ
prefix:max "↑ₜᵇ" => BTerm.shift
@[simp] theorem BSubst.shift_app : (shift x : 𝓛.BTerm (m + 1)) = #ᵇx.succ := rfl
@[simp] theorem BTerm.shift_var : ↑ₜᵇ(#ᵇx : 𝓛.BTerm m) = #ᵇx.succ := rfl

def BSubst.assign (t : 𝓛.BTerm (m + 1)) : 𝓛.BSubst (m + 1) (m + 1) :=
  t ∷ᵥ shift
prefix:max "≔ᵇ " => BSubst.assign
@[simp] theorem BSubst.assign_app_zero : (≔ᵇ t) 0 = t := rfl
@[simp] theorem BSubst.assign_app_succ {x : Fin n} : (≔ᵇ t) x.succ = #ᵇx.succ := rfl

def BSubst.lift (σ : 𝓛.BSubst m k) : 𝓛.BSubst (m + 1) (k + 1) :=
  #ᵇ0 ∷ᵥ (λ x => ↑ₜᵇ(σ x))
prefix:max "⇑ᵇ" => BSubst.lift
@[simp] theorem BSubst.lift_app_zero : ⇑ᵇσ 0 = #ᵇ0 := rfl
@[simp] theorem BSubst.lift_app_succ : ⇑ᵇσ x.succ = ↑ₜᵇ(σ x) := rfl

theorem BTerm.val_subst_eq {σ : 𝓛.BSubst m k} :
  (∀ x, (σ x).val = σ' x) → t[σ]ₜᵇ.val = t.val[σ']ₜ := by
  intro h
  induction t with simp [subst, h]
  | func f v ih => ext; apply ih _ h

theorem BTerm.val_shift_eq : (↑ₜᵇt).val = ↑ₜt.val := by
  apply BTerm.val_subst_eq; intro; rfl



inductive BFormula (𝓛 : Language) : ℕ → Type where
| rel : 𝓛.𝓡 n → (Fin n → 𝓛.BTerm m) → 𝓛.BFormula m
| eq : 𝓛.BTerm m → 𝓛.BTerm m → 𝓛.BFormula m
| false : 𝓛.BFormula m
| imp : 𝓛.BFormula m → 𝓛.BFormula m → 𝓛.BFormula m
| all : 𝓛.BFormula (m + 1) → 𝓛.BFormula m

infix:70 " ⬝ᵣᵇ " => BFormula.rel
instance : PropNotation (𝓛.BFormula m) := ⟨BFormula.false, BFormula.imp⟩
prefix:59 "∀ᵇ " => BFormula.all
abbrev BFormula.exist (p : 𝓛.BFormula (m + 1)) := ~ ∀ᵇ (~ p)
prefix:59 "∃ᵇ " => BFormula.exist

infix:60 " ≐ᵇ " => BFormula.eq

@[simp] theorem BFormula.false_eq : BFormula.false = (⊥ : 𝓛.BFormula m) := rfl
@[simp] theorem BFormula.imp_eq : BFormula.imp p q = p ⇒ q := rfl

abbrev Sentence (𝓛 : Language) := 𝓛.BFormula 0

def BFormula.alls : ∀ {m}, 𝓛.BFormula m → 𝓛.Sentence
| 0, p => p
| _ + 1, p => (∀ᵇ p).alls
prefix:59 "∀* " => BFormula.alls

def BFormula.val : 𝓛.BFormula m → 𝓛.Formula
| p ⬝ᵣᵇ v => p ⬝ᵣ (λ i => (v i).val)
| t₁ ≐ᵇ t₂ => t₁.val ≐ t₂.val
| ⊥ => ⊥
| p ⇒ q => p.val ⇒ q.val
| ∀ᵇ p => ∀' p.val
@[simp] theorem BFormula.val_rel : (p ⬝ᵣᵇ v : 𝓛.BFormula m).val = p ⬝ᵣ (λ i => (v i).val) := rfl
@[simp] theorem BFormula.val_eq : (t₁ ≐ᵇ t₂).val = t₁.val ≐ t₂.val := rfl
@[simp] theorem BFormula.val_false : (⊥ : 𝓛.BFormula m).val = ⊥ := rfl
@[simp] theorem BFormula.val_imp : (p ⇒ q : 𝓛.BFormula m).val = p.val ⇒ q.val := rfl
@[simp] theorem BFormula.val_all : (∀ᵇ p).val = ∀' p.val := rfl

@[simp] def Formula.bound : 𝓛.Formula → ℕ
| _ ⬝ᵣ v => Vec.max (λ i => (v i).bound)
| t₁ ≐ t₂ => max t₁.bound t₂.bound
| ⊥ => 0
| p ⇒ q => max p.bound q.bound
| ∀' p => p.bound - 1

theorem BFormula.property : (p : 𝓛.BFormula m).val.bound ≤ m := by
  induction p with simp
  | rel r v => apply Vec.max_le; intro; apply BTerm.property
  | eq t₁ t₂ => simp [BTerm.property]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => simp [ih]

def BFormula.mk :
  (p : 𝓛.Formula) → m ≥ p.bound → 𝓛.BFormula m
| r ⬝ᵣ v, h => r ⬝ᵣᵇ (λ i => BTerm.mk (v i) (Nat.le_trans (Vec.le_max (v := Term.bound ∘ v)) h))
| t₁ ≐ t₂, h => BTerm.mk t₁ (le_of_max_le_left h) ≐ᵇ BTerm.mk t₂ (le_of_max_le_right h)
| ⊥, _ => ⊥
| p ⇒ q, h => mk p (le_of_max_le_left h) ⇒ mk q (le_of_max_le_right h)
| ∀' p, h => ∀ᵇ (mk p (Nat.le_succ_of_pred_le h))

theorem BFormula.val_mk {p : 𝓛.Formula} {h : m ≥ p.bound} :
  (mk p h).val = p := by
  induction p generalizing m with simp [mk]
  | rel => ext; simp [BTerm.val_mk]
  | eq => simp [BTerm.val_mk]
  | imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | all _ ih => simp [ih]

def BFormula.subst : 𝓛.BFormula m → 𝓛.BSubst m k → 𝓛.BFormula k
| r ⬝ᵣᵇ v, σ => r ⬝ᵣᵇ (λ i => (v i).subst σ)
| t₁ ≐ᵇ t₂, σ => t₁.subst σ ≐ᵇ t₂.subst σ
| ⊥, _ => ⊥
| p ⇒ q, σ => p.subst σ ⇒ q.subst σ
| ∀ᵇ p, σ => ∀ᵇ (p.subst (⇑ᵇσ))
notation:80 p "[" σ "]ₚᵇ" => BFormula.subst p σ

@[simp] theorem BFormula.subst_rel : (r ⬝ᵣᵇ v)[σ]ₚᵇ = r ⬝ᵣᵇ (λ i => (v i)[σ]ₜᵇ) := rfl
@[simp] theorem BFormula.subst_eq : (t₁ ≐ᵇ t₂)[σ]ₚᵇ = t₁[σ]ₜᵇ ≐ᵇ t₂[σ]ₜᵇ := rfl
@[simp] theorem BFormula.subst_false : ⊥[σ]ₚᵇ = ⊥ := rfl
@[simp] theorem BFormula.subst_imp : (p ⇒ q)[σ]ₚᵇ = p[σ]ₚᵇ ⇒ q[σ]ₚᵇ := rfl
@[simp] theorem BFormula.subst_neg : (~ p)[σ]ₚᵇ = ~ p[σ]ₚᵇ := rfl
@[simp] theorem BFormula.subst_all : (∀ᵇ p)[σ]ₚᵇ = ∀ᵇ p[⇑ᵇσ]ₚᵇ := rfl

def BFormula.shift (p : 𝓛.BFormula m) := p[BSubst.shift]ₚᵇ
prefix:max "↑ₚᵇ" => BFormula.shift

theorem BFormula.subst_id : p[BSubst.id]ₚᵇ = p := by
  induction p <;> simp
  case imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  case all p ih =>
    conv => rhs; rw [←ih]
    congr
    funext x
    cases x using Fin.cases
    · rfl
    · simp

theorem BFormula.val_subst_eq {σ : 𝓛.BSubst m k} :
  (∀ x, (σ x).val = σ' x) → p[σ]ₚᵇ.val = p.val[σ']ₚ := by
  intro h
  induction p generalizing k σ' <;> try simp
  case rel r v => ext; simp [BTerm.val_subst_eq h]
  case eq t₁ t₂ => simp [BTerm.val_subst_eq h]
  case imp p q ih₁ ih₂ => simp [ih₁ h, ih₂ h]
  case all p ih =>
    apply ih
    intro x
    cases x using Fin.cases
    · rfl
    · simp [BTerm.val_shift_eq, h]

theorem Sentence.val_subst_eq {p : 𝓛.Sentence} :
  p.val[σ]ₚ = p.val := by
  rw [←BFormula.val_subst_eq (σ := BSubst.id) (·.elim0), BFormula.subst_id]

theorem Sentence.shift_eq {p : Sentence 𝓛} :
  ↑ₚp.val = p.val := Sentence.val_subst_eq

end FirstOrder.Language
