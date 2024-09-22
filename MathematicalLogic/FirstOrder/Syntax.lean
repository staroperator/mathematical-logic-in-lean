import Mathlib.Data.Set.Lattice
import MathematicalLogic.Vector
import MathematicalLogic.Notation

namespace FirstOrder

structure Language where
  Func : ℕ → Type
  Rel : ℕ → Type

namespace Language

variable {𝓛 : Language}

abbrev Const (𝓛 : Language) := 𝓛.Func 0

inductive Term (𝓛 : Language) (n : ℕ) : Type where
| var : Fin n → 𝓛.Term n
| func : 𝓛.Func m → (Fin m → 𝓛.Term n) → 𝓛.Term n
prefix:max "#" => Term.var
infix:70 " ⬝ₜ " => Term.func
instance : Coe 𝓛.Const (𝓛.Term n) := ⟨λ c => c ⬝ₜ []ᵥ⟩

instance Term.decEq [∀ n, DecidableEq (𝓛.Func n)] : DecidableEq (𝓛.Term n) := by
  intro t₁ t₂
  cases t₁ <;> cases t₂
  case var.var n m =>
    rw [Term.var.injEq]
    by_cases h : n = m
    · exact isTrue h
    · exact isFalse h
  case func.func n f v₁ m g v₂ =>
    by_cases h : n = m
    · subst h; simp [Term.func.injEq]; rw [Vec.ext_iff]
      have := λ i => decEq (v₁ i) (v₂ i)
      infer_instance
    · simp [h]; exact isFalse not_false
  all_goals exact isFalse Term.noConfusion

@[simp] def Term.size : 𝓛.Term n → ℕ
| #_ => 0
| _ ⬝ₜ v => (Vec.max λ i => (v i).size) + 1
instance : SizeOf (𝓛.Term n) := ⟨Term.size⟩
@[simp] theorem Term.sizeOf_lt_func : sizeOf (v i) < sizeOf (f ⬝ₜ v) :=
  Nat.lt_succ_of_le (Vec.le_max (v := λ i => (v i).size))

def Subst (𝓛 : Language) (n m : ℕ) := Vec (𝓛.Term m) n

def Term.subst : 𝓛.Term n → 𝓛.Subst n m → 𝓛.Term m
| #x, σ => σ x
| f ⬝ₜ v, σ => f ⬝ₜ λ i => (v i).subst σ
notation:80 t "[" σ "]ₜ" => Term.subst t σ
@[simp] theorem Term.subst_var : (#x)[σ]ₜ = σ x := rfl
@[simp] theorem Term.subst_func : (f ⬝ₜ v)[σ]ₜ = f ⬝ₜ λ i => (v i)[σ]ₜ := rfl
theorem Term.subst_const {c : 𝓛.Const} : (c : 𝓛.Term n)[σ]ₜ = c := by simp; apply Vec.eq_nil

def Subst.id : 𝓛.Subst n n := λ x => #x
@[simp] theorem Subst.id_app : (id x : 𝓛.Term n) = #x := rfl
@[simp] theorem Term.subst_id : t[Subst.id]ₜ = t := by
  induction t with simp
  | func f v ih => ext; apply ih

def Subst.comp (σ₁ : 𝓛.Subst n m) (σ₂ : 𝓛.Subst m k) : 𝓛.Subst n k := λ x => (σ₁ x)[σ₂]ₜ
infixl:90 " ∘ₛ " => Subst.comp
@[simp] theorem Subst.comp_app : (σ₁ ∘ₛ σ₂) x = (σ₁ x)[σ₂]ₜ := rfl
theorem Term.subst_comp : t[σ₁ ∘ₛ σ₂]ₜ = t[σ₁]ₜ[σ₂]ₜ := by
  induction t with simp
  | func f v ih => ext; apply ih

def Subst.single (t : 𝓛.Term n) : 𝓛.Subst (n + 1) n := t ∷ᵥ id
prefix:max "↦ₛ " => Subst.single
@[simp] theorem Subst.single_app_zero : (↦ₛ t) 0 = t := rfl
@[simp] theorem Subst.single_app_succ : (↦ₛ t) x.succ = #x := rfl

def Subst.shift : 𝓛.Subst n (n + 1) := λ x => #x.succ
@[simp] theorem Subst.shift_app : (shift x : 𝓛.Term (n + 1)) = #x.succ := rfl
def Term.shift (t : 𝓛.Term n) := t[Subst.shift]ₜ
prefix:max "↑ₜ" => Term.shift
@[simp] theorem Term.shift_var : ↑ₜ(#x : 𝓛.Term n) = #x.succ := rfl

def Subst.assign (t : 𝓛.Term (n + 1)) : 𝓛.Subst (n + 1) (n + 1) := t ∷ᵥ shift
prefix:max "≔ₛ " => Subst.assign
@[simp] theorem Subst.assign_app_zero : (≔ₛ t) 0 = t := rfl
@[simp] theorem Subst.assign_app_succ {x : Fin n} : (≔ₛ t) x.succ = #x.succ := rfl

theorem Term.shift_subst_cons : (↑ₜt₁)[t₂ ∷ᵥ σ]ₜ = t₁[σ]ₜ := by
  rw [shift, ←subst_comp]; rfl
theorem Term.shift_subst_single : (↑ₜt₁)[↦ₛ t₂]ₜ = t₁ := by
  simp [Subst.single]; rw [shift_subst_cons, subst_id]
theorem Term.shift_subst_assign : (↑ₜt₁)[≔ₛ t₂]ₜ = ↑ₜt₁ := shift_subst_cons

def Subst.lift (σ : 𝓛.Subst n m) : 𝓛.Subst (n + 1) (m + 1) := #0 ∷ᵥ λ x => ↑ₜ(σ x)
prefix:max "⇑ₛ" => Subst.lift
@[simp] theorem Subst.lift_app_zero : ⇑ₛσ 0 = #0 := rfl
@[simp] theorem Subst.lift_app_succ : ⇑ₛσ x.succ = ↑ₜ(σ x) := rfl
@[simp] theorem Subst.lift_app_one {σ : 𝓛.Subst (n + 1) m} : ⇑ₛσ 1 = ↑ₜ(σ 0) := rfl

theorem Term.shift_subst_lift : (↑ₜt)[⇑ₛσ]ₜ = ↑ₜ(t[σ]ₜ) := by
  simp_rw [shift, ←subst_comp]; congr
theorem Subst.lift_id : ⇑ₛ(id : 𝓛.Subst n n) = id := by
  funext x; cases x using Fin.cases <;> simp
theorem Subst.lift_comp : ⇑ₛ(σ₁ ∘ₛ σ₂) = ⇑ₛσ₁ ∘ₛ ⇑ₛσ₂ := by
  funext x; cases x using Fin.cases <;> simp [Term.shift_subst_lift]

theorem Term.subst_swap_single : t[↦ₛ t']ₜ[σ]ₜ = t[⇑ₛσ]ₜ[↦ₛ (t'[σ]ₜ)]ₜ := by
  simp_rw [←subst_comp]; congr; funext i; cases i using Fin.cases <;> simp [shift_subst_single]

def Term.vars : 𝓛.Term n → Set (Fin n)
| #x => {x}
| _ ⬝ₜ v => ⋃i, (v i).vars

theorem Term.subst_ext_vars {t : 𝓛.Term n} (h : ∀ x ∈ t.vars, σ₁ x = σ₂ x) :
  t[σ₁]ₜ = t[σ₂]ₜ := by
  induction t with simp [h, vars]
  | func t v ih => ext i; apply ih; intros; apply h; simp [vars]; exists i

theorem Term.vars_of_subst : t[σ]ₜ.vars = ⋃ x ∈ t.vars, (σ x).vars := by
  induction t with simp [vars]
  | func t v ih => rw [Set.iUnion_comm]; simp_rw [ih]



inductive Formula (𝓛 : Language) : ℕ → Type where
| rel : 𝓛.Rel m → (Fin m → 𝓛.Term n) → 𝓛.Formula n
| eq : 𝓛.Term n → 𝓛.Term n → 𝓛.Formula n
| false : 𝓛.Formula n
| imp : 𝓛.Formula n → 𝓛.Formula n → 𝓛.Formula n
| all : 𝓛.Formula (n + 1) → 𝓛.Formula n
infix:70 " ⬝ᵣ " => Formula.rel
infix:60 " ≐ " => Formula.eq
instance : PropNotation (𝓛.Formula n) := ⟨Formula.false, Formula.imp⟩
prefix:59 "∀' " => Formula.all
abbrev Formula.exist (p : 𝓛.Formula (n + 1)) := ~ ∀' (~ p)
prefix:59 "∃' " => Formula.exist

def Formula.andN : {m : ℕ} → Vec (𝓛.Formula n) m → 𝓛.Formula n
| 0, _ => ⊤
| _ + 1, v => v.head ⩑ andN v.tail
notation3:57 "⋀"(...)", " r:(scoped r => Formula.andN r) => r

def Formula.allN : (m : ℕ) → 𝓛.Formula (n + m) → 𝓛.Formula n
| 0, p => p
| m + 1, p => allN m (∀' p)
notation "∀^[" n "]" => Formula.allN n

def Formula.existsN : (m : ℕ) → 𝓛.Formula (n + m) → 𝓛.Formula n
| 0, p => p
| m + 1, p => existsN m (∃' p)
notation "∃^[" n "]" => Formula.existsN n

@[simp] theorem Formula.false_eq : Formula.false = (⊥ : 𝓛.Formula n) := rfl
@[simp] theorem Formula.imp_eq : Formula.imp p q = p ⇒ q := rfl
@[simp] theorem Formula.imp_inj {p₁ q₁ p₂ q₂ : 𝓛.Formula n} : (p₁ ⇒ q₁) = p₂ ⇒ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
  iff_of_eq (imp.injEq _ _ _ _)

@[simp] def Formula.size : 𝓛.Formula n → ℕ
| _ ⬝ᵣ _ | _ ≐ _ | ⊥ => 0
| p ⇒ q => p.size + q.size + 1
| ∀' p => p.size + 1
instance : SizeOf (𝓛.Formula n) := ⟨Formula.size⟩
@[simp] theorem Formula.sizeOf_lt_imp_left {p q : 𝓛.Formula n} : sizeOf p < sizeOf (p ⇒ q) :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)
@[simp] theorem Formula.sizeOf_lt_imp_right {p q : 𝓛.Formula n} : sizeOf q < sizeOf (p ⇒ q) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)
@[simp] theorem Formula.sizeOf_lt_all {p : 𝓛.Formula (n + 1)} : sizeOf p < sizeOf (∀' p) :=
  Nat.lt_succ_self _

instance Formula.decEq [∀ n, DecidableEq (𝓛.Func n)] [∀ n, DecidableEq (𝓛.Rel n)] : DecidableEq (𝓛.Formula n) := by
  intro p q
  cases p <;> cases q
  case rel.rel n r₁ v₁ m r₂ v₂ =>
    by_cases h : n = m
    · subst h; simp [rel.injEq]; rw [Vec.ext_iff]; infer_instance
    · simp [h]; exact isFalse not_false
  case eq.eq =>
    rw [eq.injEq]; infer_instance
  case false.false => exact isTrue rfl
  case imp.imp p₁ q₁ p₂ q₂ =>
    rw [imp.injEq]
    have := decEq p₁ p₂
    have := decEq q₁ q₂
    infer_instance
  case all.all p q =>
    rw [all.injEq]
    exact decEq p q
  all_goals exact isFalse Formula.noConfusion

def Formula.subst : 𝓛.Formula n → 𝓛.Subst n m → 𝓛.Formula m
| r ⬝ᵣ v, σ => r ⬝ᵣ λ i => (v i)[σ]ₜ
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

theorem Formula.subst_andN {v : Vec (𝓛.Formula n) m} : (⋀i, v i)[σ]ₚ = ⋀i, (v i)[σ]ₚ := by
  induction m with
  | zero => rfl
  | succ n ih => simp [andN, Vec.head, Vec.tail, PropNotation.and]; apply ih

def Formula.shift (p : 𝓛.Formula n) : 𝓛.Formula (n + 1) := p[Subst.shift]ₚ
prefix:max "↑ₚ" => Formula.shift

abbrev Formula.existUnique (p : 𝓛.Formula (n + 1)) :=
  ∃' (p ⩑ ∀' (p[⇑ₛSubst.shift]ₚ ⇒ #0 ≐ #1))
prefix:59 "∃!' " => Formula.existUnique

theorem Formula.subst_id : p[Subst.id]ₚ = p := by
  induction p with simp
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => simp [Subst.lift_id, ih]

theorem Formula.subst_comp {σ₁ : 𝓛.Subst n m} {σ₂ : 𝓛.Subst m k} : p[σ₁ ∘ₛ σ₂]ₚ = p[σ₁]ₚ[σ₂]ₚ := by
  induction p generalizing m k with simp [Term.subst_comp]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => simp [Subst.lift_comp, ih]

theorem Formula.shift_subst_single : (↑ₚp)[↦ₛ t₂]ₚ = p := by
  rw [shift, ←subst_comp]; nth_rw 2 [←subst_id (p := p)]; rfl

theorem Formula.shift_subst_lift : (↑ₚp)[⇑ₛσ]ₚ = ↑ₚ(p[σ]ₚ) := by
  simp_rw [shift, ←subst_comp]; congr

theorem Formula.subst_swap_single : p[↦ₛ t]ₚ[σ]ₚ = p[⇑ₛσ]ₚ[↦ₛ (t[σ]ₜ)]ₚ := by
  simp_rw [←subst_comp]; congr; funext i; cases i using Fin.cases <;> simp [Term.shift_subst_single]

def Formula.free : 𝓛.Formula n → Set (Fin n)
| _ ⬝ᵣ v => ⋃i, (v i).vars
| t₁ ≐ t₂ => t₁.vars ∪ t₂.vars
| ⊥ => ∅
| p ⇒ q => p.free ∪ q.free
| ∀' p => { x | x.succ ∈ p.free }

theorem Formula.subst_ext_free {p : 𝓛.Formula n} {σ₁ σ₂ : 𝓛.Subst n m} :
  (∀ x ∈ p.free, σ₁ x = σ₂ x) → p[σ₁]ₚ = p[σ₂]ₚ := by
  intro h
  induction p generalizing m with simp
  | rel =>
    ext i; apply Term.subst_ext_vars
    intros; apply h; simp [free]
    exists i
  | eq =>
    constructor <;> apply Term.subst_ext_vars <;> intros _ h₁ <;> apply h <;> simp [free, h₁]
  | imp p q ih₁ ih₂ =>
    constructor <;> apply_assumption <;> intros _ h₁ <;> apply h <;> simp [free, h₁]
  | all _ ih =>
    apply ih; intro x h₁
    cases x using Fin.cases with simp
    | succ x => congr; apply h; simp [free]; exact h₁

theorem Formula.free_of_subst {σ : 𝓛.Subst n m} :
  p[σ]ₚ.free = ⋃ x ∈ p.free, (σ x).vars := by
  induction p generalizing m with simp_rw [free]
  | rel => simp [Term.vars_of_subst]; rw [Set.iUnion_comm]
  | eq => simp [Set.iUnion_or, Set.iUnion_union_distrib, Term.vars_of_subst]
  | false => simp
  | imp p q ih₁ ih₂ => rw [ih₁, ih₂, Set.biUnion_union]
  | all p ih =>
    ext x; simp [ih]
    constructor
    · rintro ⟨y, h₁, h₂⟩
      cases y using Fin.cases with
      | zero => simp [Term.vars] at h₂; simp [Fin.succ_ne_zero] at h₂
      | succ y =>
        simp [Subst.lift, Term.shift, Term.vars_of_subst] at h₂
        rcases h₂ with ⟨z, h₂, h₃⟩
        simp [Subst.shift, Term.vars] at h₃
        subst h₃
        exists y
    · rintro ⟨y, ⟨h₁, h₂⟩⟩
      exists y.succ
      constructor
      · exact h₁
      · simp [Subst.lift, Term.shift, Term.vars_of_subst]
        exists x

abbrev Sentence (𝓛 : Language) := 𝓛.Formula 0

def Formula.alls : {n : ℕ} → 𝓛.Formula n → 𝓛.Sentence
| 0, p => p
| _ + 1, p => alls (∀' p)
prefix:59 "∀*" => Formula.alls

abbrev FormulaSet (𝓛 : Language) (n : ℕ) := Set (𝓛.Formula n)

abbrev FormulaSet.append (Γ : 𝓛.FormulaSet n) (p : 𝓛.Formula n) := insert p Γ
infixl:51 ",' " => FormulaSet.append

abbrev FormulaSet.shift (Γ : 𝓛.FormulaSet n) : 𝓛.FormulaSet (n + 1) := (↑ₚ ·) '' Γ
prefix:max "↑ᴳ" => FormulaSet.shift
@[simp] theorem FormulaSet.shift_empty : ↑ᴳ(∅ : 𝓛.FormulaSet n) = ∅ := Set.image_empty _
@[simp] theorem FormulaSet.shift_append : ↑ᴳ(Γ,' p) = ↑ᴳΓ,' ↑ₚp := Set.image_insert_eq

abbrev Theory (𝓛 : Language) := 𝓛.FormulaSet 0

def Theory.shiftN : (n : ℕ) → 𝓛.Theory → 𝓛.FormulaSet n
| 0, 𝓣 => 𝓣
| n + 1, 𝓣 => ↑ᴳ(𝓣.shiftN n)
notation "↑ᴳ^[" n "]" => Theory.shiftN n

end FirstOrder.Language
