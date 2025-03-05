import MathematicalLogic.Vec
import MathematicalLogic.Notation

namespace FirstOrder

structure Language where
  Func : ℕ → Type
  Rel : ℕ → Type

namespace Language

variable {L : Language}

abbrev Const (L : Language) := L.Func 0

inductive Term (L : Language) (n : ℕ) : Type where
| var : Fin n → L.Term n
| func : L.Func m → (Fin m → L.Term n) → L.Term n

namespace Term

prefix:max "#" => var
infix:70 " ⬝ᶠ " => func
instance : Coe L.Const (L.Term n) := ⟨λ c => c ⬝ᶠ []ᵥ⟩

instance decEq [∀ n, DecidableEq (L.Func n)] : DecidableEq (L.Term n) := by
  intro t₁ t₂
  cases t₁ <;> cases t₂
  case var.var n m =>
    rw [var.injEq]
    by_cases h : n = m
    · exact isTrue h
    · exact isFalse h
  case func.func n f v₁ m g v₂ =>
    by_cases h : n = m
    · subst h; simp [func.injEq]; rw [Vec.ext_iff]
      have := λ i => decEq (v₁ i) (v₂ i)
      infer_instance
    · simp [h]; exact isFalse not_false
  all_goals exact isFalse Term.noConfusion

@[simp] def size : L.Term n → ℕ
| #_ => 0
| _ ⬝ᶠ v => (Vec.max λ i => (v i).size) + 1
instance : SizeOf (L.Term n) := ⟨size⟩
@[simp] theorem sizeOf_lt_func : sizeOf (v i) < sizeOf (f ⬝ᶠ v) :=
  Nat.lt_succ_of_le (Vec.le_max (v := λ i => (v i).size) i)

end Term

abbrev Subst (L : Language) (n m : ℕ) := Vec (L.Term m) n

def Term.subst : L.Term n → L.Subst n m → L.Term m
| #x, σ => σ x
| f ⬝ᶠ v, σ => f ⬝ᶠ λ i => (v i).subst σ
macro:max t:term noWs "[" σ:term "]ₜ" : term => `(Term.subst $t $σ)
@[app_unexpander Term.subst] def Term.unexpandSubst : Lean.PrettyPrinter.Unexpander
| `($_ $t $σ) => `($t[$σ]ₜ)
| _ => throw ()

@[simp] theorem Term.subst_var : (#x)[σ]ₜ = σ x := rfl
@[simp] theorem Term.subst_func : (f ⬝ᶠ v)[σ]ₜ = f ⬝ᶠ λ i => (v i)[σ]ₜ := rfl
theorem Term.subst_const {c : L.Const} : (c : L.Term n)[σ]ₜ = c := by simp; apply Vec.eq_nil

def Subst.id : L.Subst n n := λ x => #x
@[simp] theorem Subst.id_app : (id x : L.Term n) = #x := rfl
@[simp] theorem Term.subst_id (t : L.Term n) : t[Subst.id]ₜ = t := by
  induction t with simp
  | func f v ih => ext; apply ih

def Subst.comp (σ₁ : L.Subst n m) (σ₂ : L.Subst m k) : L.Subst n k := λ x => (σ₁ x)[σ₂]ₜ
infixl:90 " ∘ₛ " => Subst.comp
theorem Subst.comp_def : σ₁ ∘ₛ σ₂ = λ x => (σ₁ x)[σ₂]ₜ := rfl
@[simp] theorem Subst.comp_app : (σ₁ ∘ₛ σ₂) x = (σ₁ x)[σ₂]ₜ := rfl
theorem Term.subst_comp : t[σ₁ ∘ₛ σ₂]ₜ = t[σ₁]ₜ[σ₂]ₜ := by
  induction t with simp
  | func f v ih => ext; apply ih

def Subst.single (t : L.Term n) : L.Subst (n + 1) n := t ∷ᵥ id
prefix:lead "↦ₛ " => Subst.single
@[simp] theorem Subst.single_app_zero : (↦ₛ t) 0 = t := rfl
@[simp] theorem Subst.single_app_succ : (↦ₛ t) x.succ = #x := rfl
@[simp] theorem Subst.single_app_one {t : L.Term (n + 1)} : (↦ₛ t) 1 = #0 := rfl

def Subst.shift : L.Subst n (n + 1) := λ x => #x.succ
@[simp] theorem Subst.shift_app : (shift x : L.Term (n + 1)) = #x.succ := rfl
def Term.shift (t : L.Term n) := t[Subst.shift]ₜ
prefix:max "↑ₜ" => Term.shift
@[simp] theorem Term.shift_var : ↑ₜ(#x : L.Term n) = #x.succ := rfl

def Subst.assign (t : L.Term (n + 1)) : L.Subst (n + 1) (n + 1) := t ∷ᵥ shift
prefix:lead "≔ₛ " => Subst.assign
@[simp] theorem Subst.assign_app_zero : (≔ₛ t) 0 = t := rfl
@[simp] theorem Subst.assign_app_succ {x : Fin n} : (≔ₛ t) x.succ = #x.succ := rfl
theorem Subst.assign_zero : ≔ₛ #0 = @id L (n + 1) := by
  ext x; cases x using Fin.cases <;> simp

theorem Term.shift_subst_cons : (↑ₜt₁)[t₂ ∷ᵥ σ]ₜ = t₁[σ]ₜ := by
  rw [shift, ←subst_comp]; rfl
theorem Term.shift_subst_single : (↑ₜt₁)[↦ₛ t₂]ₜ = t₁ := by
  simp [Subst.single]; rw [shift_subst_cons, subst_id]
theorem Term.shift_subst_assign : (↑ₜt₁)[≔ₛ t₂]ₜ = ↑ₜt₁ := shift_subst_cons

def Subst.lift (σ : L.Subst n m) : L.Subst (n + 1) (m + 1) := #0 ∷ᵥ λ x => ↑ₜ(σ x)
prefix:max "⇑ₛ" => Subst.lift
@[simp] theorem Subst.lift_app_zero : ⇑ₛσ 0 = #0 := rfl
@[simp] theorem Subst.lift_app_succ : ⇑ₛσ x.succ = ↑ₜ(σ x) := rfl
@[simp] theorem Subst.lift_app_one {σ : L.Subst (n + 1) m} : ⇑ₛσ 1 = ↑ₜ(σ 0) := rfl

theorem Term.shift_subst_lift : (↑ₜt)[⇑ₛσ]ₜ = ↑ₜ(t[σ]ₜ) := by
  simp_rw [shift, ←subst_comp]; congr
theorem Subst.lift_id : ⇑ₛ(id : L.Subst n n) = id := by
  funext x; cases x using Fin.cases <;> simp
theorem Subst.lift_comp : ⇑ₛ(σ₁ ∘ₛ σ₂) = ⇑ₛσ₁ ∘ₛ ⇑ₛσ₂ := by
  funext x; cases x using Fin.cases <;> simp [Term.shift_subst_lift]

theorem Subst.lift_comp_single : ⇑ₛσ ∘ₛ ↦ₛ t = t ∷ᵥ σ := by
  ext x; cases x using Fin.cases <;> simp [Term.shift_subst_single]
theorem Subst.cons_comp : (t ∷ᵥ σ₁) ∘ₛ σ₂ = t[σ₂]ₜ ∷ᵥ σ₁ ∘ₛ σ₂ := by
  ext x; cases x using Fin.cases <;> simp
theorem Subst.single_comp : ↦ₛ t ∘ₛ σ = t[σ]ₜ ∷ᵥ σ := cons_comp

theorem Term.subst_swap_single : t[↦ₛ t']ₜ[σ]ₜ = t[⇑ₛσ]ₜ[↦ₛ t'[σ]ₜ]ₜ := by
  simp [←subst_comp, Subst.lift_comp_single, Subst.single_comp]

def Term.shiftN : (m : ℕ) → L.Term n → L.Term (n + m)
| 0, t => t
| m + 1, t => ↑ₜ(shiftN m t)
notation "↑ₜ^[" m "]" => Term.shiftN m
theorem Term.shiftN_eq_subst : ↑ₜ^[m] t = t[λ i => #(i.addNat m)]ₜ := by
  induction m with simp [shiftN]
  | zero => nth_rw 1 [←subst_id t]; rfl
  | succ m ih => rw [ih, shift, ←subst_comp]; rfl
@[simp] theorem Term.shiftN_var : ↑ₜ^[m] (#x : L.Term n) = #(x.addNat m) := by
  simp [Term.shiftN_eq_subst]

def Subst.liftN : (m : ℕ) → L.Subst n k → L.Subst (n + m) (k + m)
| 0, σ => σ
| m + 1, σ => ⇑ₛ(liftN m σ)
notation "⇑ₛ^[" m "]" => Subst.liftN m
@[simp] theorem Subst.liftN_app_addNat {σ : L.Subst n k} : ⇑ₛ^[m] σ (Fin.addNat x m) = ↑ₜ^[m] (σ x) := by
  induction m with simp [liftN, Term.shiftN]
  | succ m ih => simp [ih]
@[simp] theorem Subst.liftN_app_castAdd' {σ : L.Subst n k} : ⇑ₛ^[m] σ (Fin.castAdd' x n) = #(Fin.castAdd' x k) := by
  induction m with simp [liftN]
  | zero => exact x.elim0
  | succ m ih => cases x using Fin.cases <;> simp [ih]

theorem Term.shiftN_subst_liftN : (↑ₜ^[m] t)[⇑ₛ^[m] σ]ₜ = ↑ₜ^[m] (t[σ]ₜ) := by
  induction m with simp [shiftN, Subst.liftN]
  | succ m ih => simp [shift_subst_lift, ih]

def Term.vars : L.Term n → Set (Fin n)
| #x => {x}
| _ ⬝ᶠ v => ⋃i, (v i).vars

theorem Term.subst_ext_vars {t : L.Term n} (h : ∀ x ∈ t.vars, σ₁ x = σ₂ x) :
  t[σ₁]ₜ = t[σ₂]ₜ := by
  induction t with simp [h, vars]
  | func t v ih => ext i; apply ih; intros; apply h; simp [vars]; exists i

theorem Term.vars_of_subst : t[σ]ₜ.vars = ⋃ x ∈ t.vars, (σ x).vars := by
  induction t with simp [vars]
  | func t v ih => rw [Set.iUnion_comm]; simp_rw [ih]



inductive Formula (L : Language) : ℕ → Type where
| rel : L.Rel m → (Fin m → L.Term n) → L.Formula n
| eq : L.Term n → L.Term n → L.Formula n
| false : L.Formula n
| imp : L.Formula n → L.Formula n → L.Formula n
| all : L.Formula (n + 1) → L.Formula n

namespace Formula

infix:70 " ⬝ʳ " => rel
infix:60 " ≐ " => eq
instance : PropNotation (L.Formula n) := ⟨false, imp⟩
prefix:max "∀' " => all
def ex (p : L.Formula (n + 1)) := ~ ∀' (~ p)
prefix:max "∃' " => ex

def andN : {m : ℕ} → Vec (L.Formula n) m → L.Formula n
| 0, _ => ⊤
| _ + 1, v => v.head ⩑ andN v.tail
notation3 "⋀ "(...)", " r:52:(scoped r => andN r) => r

def orN : {m : ℕ} → Vec (L.Formula n) m → L.Formula n
| 0, _ => ⊥
| _ + 1, v => v.head ⩒ orN v.tail
notation3 "⋁ "(...)", " r:52:(scoped r => orN r) => r

def allN : (m : ℕ) → L.Formula (n + m) → L.Formula n
| 0, p => p
| m + 1, p => allN m (∀' p)
notation "∀^[" n "]" => allN n

def exN : (m : ℕ) → L.Formula (n + m) → L.Formula n
| 0, p => p
| m + 1, p => exN m (∃' p)
notation "∃^[" n "]" => exN n

@[simp] theorem false_eq : false = (⊥ : L.Formula n) := rfl
@[simp] theorem imp_eq : imp p q = p ⇒ q := rfl
@[simp] theorem neg_eq {p : L.Formula n} : (p ⇒ ⊥) = ~ p := rfl
@[simp] theorem imp_inj {p₁ q₁ p₂ q₂ : L.Formula n} : (p₁ ⇒ q₁) = p₂ ⇒ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
  iff_of_eq (imp.injEq _ _ _ _)

@[simp] def size : L.Formula n → ℕ
| _ ⬝ʳ _ | _ ≐ _ | ⊥ => 0
| p ⇒ q => p.size + q.size + 1
| ∀' p => p.size + 1
instance : SizeOf (L.Formula n) := ⟨size⟩
@[simp] theorem sizeOf_lt_imp_left {p q : L.Formula n} : sizeOf p < sizeOf (p ⇒ q) :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)
@[simp] theorem sizeOf_lt_imp_right {p q : L.Formula n} : sizeOf q < sizeOf (p ⇒ q) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)
@[simp] theorem sizeOf_lt_all {p : L.Formula (n + 1)} : sizeOf p < sizeOf (∀' p) :=
  Nat.lt_succ_self _

instance decEq [∀ n, DecidableEq (L.Func n)] [∀ n, DecidableEq (L.Rel n)] : DecidableEq (L.Formula n) := by
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

def subst : L.Formula n → L.Subst n m → L.Formula m
| r ⬝ʳ v, σ => r ⬝ʳ λ i => (v i)[σ]ₜ
| t₁ ≐ t₂, σ => t₁.subst σ ≐ t₂.subst σ
| ⊥, _ => ⊥
| p ⇒ q, σ => p.subst σ ⇒ q.subst σ
| ∀' p, σ => ∀' (p.subst ⇑ₛσ)
macro:max p:term noWs "[" σ:term "]ₚ" : term => `(subst $p $σ)
@[app_unexpander subst] def unexpandSubst : Lean.PrettyPrinter.Unexpander
| `($_ $p $σ) => `($p[$σ]ₚ)
| _ => throw ()

@[simp] theorem subst_rel : (r ⬝ʳ ts)[σ]ₚ = r ⬝ʳ λ i => (ts i)[σ]ₜ := rfl
@[simp] theorem subst_eq : (t₁ ≐ t₂)[σ]ₚ = t₁[σ]ₜ ≐ t₂[σ]ₜ := rfl
@[simp] theorem subst_false : ⊥[σ]ₚ = ⊥ := rfl
@[simp] theorem subst_imp : (p ⇒ q)[σ]ₚ = p[σ]ₚ ⇒ q[σ]ₚ := rfl
@[simp] theorem subst_true : ⊤[σ]ₚ = ⊤ := rfl
@[simp] theorem subst_neg : (~ p)[σ]ₚ = ~ p[σ]ₚ := rfl
@[simp] theorem subst_and : (p ⩑ q)[σ]ₚ = p[σ]ₚ ⩑ q[σ]ₚ := rfl
@[simp] theorem subst_or : (p ⩒ q)[σ]ₚ = p[σ]ₚ ⩒ q[σ]ₚ := rfl
@[simp] theorem subst_iff : (p ⇔ q)[σ]ₚ = p[σ]ₚ ⇔ q[σ]ₚ := rfl
@[simp] theorem subst_all : (∀' p)[σ]ₚ = ∀' (p[⇑ₛσ]ₚ) := rfl
@[simp] theorem subst_ex : (∃' p)[σ]ₚ = ∃' (p[⇑ₛσ]ₚ) := rfl

theorem subst_andN {v : Vec (L.Formula n) m} : (⋀ i, v i)[σ]ₚ = ⋀ i, (v i)[σ]ₚ := by
  induction m with
  | zero => rfl
  | succ n ih => simp [andN, Vec.head, Vec.tail, Function.comp_def, ih]

theorem subst_allN : (∀^[m] p)[σ]ₚ = ∀^[m] (p[⇑ₛ^[m] σ]ₚ) := by
  induction m with simp [allN, Subst.liftN]
  | succ m ih => simp [ih]

theorem subst_exN : (∃^[m] p)[σ]ₚ = ∃^[m] (p[⇑ₛ^[m] σ]ₚ) := by
  induction m with simp [exN, Subst.liftN]
  | succ m ih => simp [ih]

def shift (p : L.Formula n) : L.Formula (n + 1) := p[Subst.shift]ₚ
prefix:max "↑ₚ" => shift
@[simp] theorem shift_eq : ↑ₚ(t₁ ≐ t₂) = ↑ₜt₁ ≐ ↑ₜt₂ := rfl
@[simp] theorem shift_false : ↑ₚ(⊥ : L.Formula n) = ⊥ := rfl
@[simp] theorem shift_imp : ↑ₚ(p ⇒ q) = ↑ₚp ⇒ ↑ₚq := rfl
@[simp] theorem shift_neg : ↑ₚ(~ p) = ~ ↑ₚp := rfl
@[simp] theorem shift_and : ↑ₚ(p ⩑ q) = ↑ₚp ⩑ ↑ₚq := rfl
@[simp] theorem shift_or : ↑ₚ(p ⩒ q) = ↑ₚp ⩒ ↑ₚq := rfl

theorem subst_id (p : L.Formula n) : p[Subst.id]ₚ = p := by
  induction p with simp
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => simp [Subst.lift_id, ih]

theorem subst_comp {σ₁ : L.Subst n m} {σ₂ : L.Subst m k} : p[σ₁ ∘ₛ σ₂]ₚ = p[σ₁]ₚ[σ₂]ₚ := by
  induction p generalizing m k with simp [Term.subst_comp]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => simp [Subst.lift_comp, ih]

theorem shift_subst_cons : (↑ₚp)[t ∷ᵥ σ]ₚ = p[σ]ₚ := by
  rw [shift, ←subst_comp]; rfl

theorem shift_subst_single : (↑ₚp)[↦ₛ t]ₚ = p := by
  simp [Subst.single]; rw [shift_subst_cons, subst_id]

theorem shift_subst_assign : (↑ₚp)[≔ₛ t]ₚ = ↑ₚp := shift_subst_cons

theorem shift_subst_lift : (↑ₚp)[⇑ₛσ]ₚ = ↑ₚ(p[σ]ₚ) := by
  simp_rw [shift, ←subst_comp]; congr

theorem subst_swap_single : p[↦ₛ t]ₚ[σ]ₚ = p[⇑ₛσ]ₚ[↦ₛ t[σ]ₜ]ₚ := by
  simp_rw [←subst_comp]; congr; funext i; cases i using Fin.cases <;> simp [Term.shift_subst_single]

def exUnique (p : L.Formula (n + 1)) :=
  ∃' (p ⩑ ∀' (p[⇑ₛSubst.shift]ₚ ⇒ #0 ≐ #1))
prefix:max "∃!' " => exUnique

def shiftN : (m : ℕ) → L.Formula n → L.Formula (n + m)
| 0, p => p
| m + 1, p => ↑ₚ(shiftN m p)
notation "↑ₚ^[" m "]" => shiftN m
theorem shiftN_eq_subst : ↑ₚ^[m] p = p[λ i => #(i.addNat m)]ₚ := by
  induction m with simp [shiftN]
  | zero => nth_rw 1 [←subst_id p]; rfl
  | succ m ih => rw [ih, shift, ←subst_comp]; rfl
@[simp] theorem shiftN_eq : ↑ₚ^[m] (t₁ ≐ t₂) = ↑ₜ^[m] t₁ ≐ ↑ₜ^[m] t₂ := by
  induction m with simp [shiftN, Term.shiftN]
  | succ m ih => simp [ih]

theorem shiftN_subst_liftN : (↑ₚ^[m] p)[⇑ₛ^[m] σ]ₚ = ↑ₚ^[m] (p[σ]ₚ) := by
  induction m with simp [shiftN, Subst.liftN]
  | succ m ih => simp [shift_subst_lift, ih]

def free : L.Formula n → Set (Fin n)
| _ ⬝ʳ v => ⋃i, (v i).vars
| t₁ ≐ t₂ => t₁.vars ∪ t₂.vars
| ⊥ => ∅
| p ⇒ q => p.free ∪ q.free
| ∀' p => { x | x.succ ∈ p.free }

theorem subst_ext_free {p : L.Formula n} {σ₁ σ₂ : L.Subst n m} :
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

theorem free_of_subst {σ : L.Subst n m} :
  p[σ]ₚ.free = ⋃ x ∈ p.free, (σ x).vars := by
  induction p generalizing m with simp [free]
  | rel => simp [Term.vars_of_subst]; rw [Set.iUnion_comm]
  | eq => simp [Set.iUnion_or, Set.iUnion_union_distrib, Term.vars_of_subst]
  | imp p q ih₁ ih₂ => simp_rw [Set.iUnion_or]; rw [ih₁, ih₂, Set.iUnion_union_distrib]
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

end Formula

abbrev Sentence (L : Language) := L.Formula 0

theorem Sentence.subst_nil {p : L.Sentence} {σ : L.Subst 0 0} : p[σ]ₚ = p := by
  nth_rw 2 [←Formula.subst_id p]
  simp [Vec.eq_nil]

def Formula.alls : {n : ℕ} → L.Formula n → L.Sentence
| 0, p => p
| _ + 1, p => alls (∀' p)
prefix:max "∀* " => Formula.alls

abbrev FormulaSet (L : Language) (n : ℕ) := Set (L.Formula n)

def FormulaSet.append (Γ : L.FormulaSet n) (p : L.Formula n) := insert p Γ
infixl:51 ",' " => FormulaSet.append

theorem FormulaSet.append_comm : Γ,' p,' q = Γ,' q,' p := Set.insert_comm _ _ _
theorem FormulaSet.append_eq_append : Γ = Δ → Γ,' p = Δ,' p := by intro h; rw [h]
theorem FormulaSet.subset_of_eq {Γ : L.FormulaSet n} : Γ = Δ → Γ ⊆ Δ := by intro h; rw [h]
theorem FormulaSet.mem_append : p ∈ Γ,' p := Set.mem_insert _ _
theorem FormulaSet.subset_append : Γ ⊆ Γ,' p := Set.subset_insert _ _
theorem FormulaSet.append_subset_append : Γ ⊆ Δ → Γ,' p ⊆ Δ,' p := Set.insert_subset_insert

def FormulaSet.shift (Γ : L.FormulaSet n) : L.FormulaSet (n + 1) := (↑ₚ ·) '' Γ
prefix:max "↑ᴳ" => FormulaSet.shift
@[simp] theorem FormulaSet.shift_empty : ↑ᴳ(∅ : L.FormulaSet n) = ∅ := Set.image_empty _
@[simp] theorem FormulaSet.shift_append : ↑ᴳ(Γ,' p) = ↑ᴳΓ,' ↑ₚp := Set.image_insert_eq

@[reducible] def FormulaSet.shiftN : (m : ℕ) → L.FormulaSet n → L.FormulaSet (n + m)
| 0, Γ => Γ
| m + 1, Γ => ↑ᴳ(Γ.shiftN m)
notation "↑ᴳ^[" n "]" => FormulaSet.shiftN n
@[simp] theorem FormulaSet.shiftN_empty : ↑ᴳ^[m] (∅ : L.FormulaSet n) = ∅ := by
  induction m with simp [shiftN]
  | succ m ih => simp [ih]
@[simp] theorem FormulaSet.shiftN_append {Γ : L.FormulaSet n} :
  ↑ᴳ^[m] (Γ,' p) = ↑ᴳ^[m] Γ,' ↑ₚ^[m] p := by
  induction m with simp [shiftN, Formula.shiftN]
  | succ m ih => simp [ih]

abbrev Theory (L : Language) := Set L.Sentence

@[reducible] def Theory.shiftN : (n : ℕ) → L.Theory → L.FormulaSet n
| 0, T => T
| n + 1, T => ↑ᴳ(T.shiftN n)
notation "↑ᵀ^[" n "]" => Theory.shiftN n
@[simp] theorem Theory.shift_shiftN : ↑ᴳ (↑ᵀ^[n] T) = ↑ᵀ^[n + 1] T := rfl
@[simp] theorem Theory.shiftN_shiftN : ↑ᴳ^[m] (↑ᵀ^[n] T) = ↑ᵀ^[n + m] T := by
  induction m with simp [FormulaSet.shiftN]
  | succ m ih => simp [ih]; rfl

end FirstOrder.Language
