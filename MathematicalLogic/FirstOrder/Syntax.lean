import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.BoundedOrder

structure Language where
  𝓕 : ℕ → Type
  𝓟 : ℕ → Type

def Const (𝓛 : Language) := 𝓛.𝓕 0

mutual
inductive Term : Language → Type where
| var : ℕ → Term 𝓛
| func : 𝓛.𝓕 n → Terms 𝓛 n → Term 𝓛
inductive Terms : Language → ℕ → Type where
| nil : Terms 𝓛 0
| cons : Term 𝓛 → Terms 𝓛 n → Terms 𝓛 (n + 1)
end

prefix:max "#" => Term.var
infix:70 " ⬝ₜ " => Term.func
infixr:67 " ∷ₜ " => Terms.cons
syntax "[" withoutPosition(term,*) "]ₜ"  : term
macro_rules
  | `([ $elems,* ]ₜ) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Lean.TSyntax `term) : Lean.MacroM Lean.Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(Terms.cons $(⟨elems.elemsAndSeps.get! i⟩) $result))
    expandListLit elems.elemsAndSeps.size false (← ``(Terms.nil))

mutual
@[simp] def Term.size : Term 𝓛 → ℕ
| #_ => 0
| _ ⬝ₜ ts => ts.size + 1
@[simp] def Terms.size : Terms 𝓛 n → ℕ
| []ₜ => 0
| t ∷ₜ ts => t.size + ts.size + 1
end

mutual
def Term.vars : Term 𝓛 → Set ℕ
| #x => {x}
| _ ⬝ₜ ts => ts.vars
def Terms.vars : Terms 𝓛 n → Set ℕ
| []ₜ => {}
| t ∷ₜ ts => t.vars ∪ ts.vars
end



def Subst (𝓛) := ℕ → Term 𝓛

mutual
def Term.subst : Term 𝓛 → Subst 𝓛 → Term 𝓛
| #x, σ => σ x
| f ⬝ₜ ts, σ => f ⬝ₜ (ts.subst σ)
def Terms.subst : Terms 𝓛 n → Subst 𝓛 → Terms 𝓛 n
| []ₜ, _ => []ₜ
| t ∷ₜ ts, σ => t.subst σ ∷ₜ ts.subst σ
end

notation:max t "[" σ "]ₜ" => Term.subst t σ
notation:max ts "[" σ "]ₜₛ" => Terms.subst ts σ

theorem Term.subst_ext : σ₁ = σ₂ → t[σ₁]ₜ = t[σ₂]ₜ := by intro h; rw [h]

def Subst.id : Subst 𝓛 := λ x => #x
mutual
theorem Term.subst_id : t[Subst.id]ₜ = t := match t with
| #x => by rw [Term.subst]; rfl
| f ⬝ₜ ts => by rw [Term.subst, Terms.subst_id]
theorem Terms.subst_id : ts[Subst.id]ₜₛ = ts := match ts with
| []ₜ => by rfl
| t ∷ₜ ts => by rw [Terms.subst, Term.subst_id, Terms.subst_id]
end

def Subst.comp (σ₁ σ₂ : Subst 𝓛) : Subst 𝓛 := λ x => (σ₁ x)[σ₂]ₜ
infixl:90 " ∘ₛ " => Subst.comp
mutual
theorem Term.subst_comp : t[σ₁]ₜ[σ₂]ₜ = t[σ₁ ∘ₛ σ₂]ₜ := match t with
| #x => by simp [Term.subst]; rfl
| f ⬝ₜ ts => by simp [Term.subst]; rw [Terms.subst_comp]
theorem Terms.subst_comp : ts[σ₁]ₜₛ[σ₂]ₜₛ = ts[σ₁ ∘ₛ σ₂]ₜₛ := match ts with
| []ₜ => by rfl
| t ∷ₜ ts => by simp only [Terms.subst]; rw [Term.subst_comp, Terms.subst_comp]
end

def Subst.single : Term 𝓛 → Subst 𝓛
| t, 0 => t
| _, x + 1 => #x
prefix:max "↦ₛ " => Subst.single

def Subst.shift : Subst 𝓛 := λ x => #(x + 1)
def Term.shift (t : Term 𝓛) := t[Subst.shift]ₜ
prefix:max "↑ₜ" => Term.shift

@[simp] theorem shift_of_var : ↑ₜ(#x : Term 𝓛) = #(x+1)
  := by simp [Term.shift, Term.subst, Subst.shift]

theorem Term.shift_subst_single : (↑ₜt₁)[↦ₛ t₂]ₜ = t₁ := by
  rw [Term.shift, Term.subst_comp]
  conv => rhs; rw [←@Term.subst_id _ t₁]

mutual
theorem Term.is_shift_iff : (∃ t', t = ↑ₜt') ↔ 0 ∉ t.vars := match t with
| #x => by
  constructor
  · rintro ⟨t', h⟩ h'
    cases t' with
    | var y =>
      rw [Term.shift, Term.subst, Subst.shift] at h
      injection h with h
      subst h
      contradiction
    | func => rw [Term.shift, Term.subst] at h; injection h
  · intro h
    cases x with
    | zero => contradiction
    | succ x => exists #x; rw [Term.shift, Term.subst, Subst.shift]
| f ⬝ₜ ts => by
  rw [Term.vars, ←Terms.is_shift_iff]
  constructor
  · rintro ⟨t', h⟩
    cases t' with
    | var => rw [Term.shift, Term.subst] at h; injection h
    | func =>
      rw [Term.shift, Term.subst] at h
      injection h with h₁ h₂ h
      subst h₁; simp at h₂; subst h₂; simp at h; subst h
      refine ⟨_, rfl⟩
  · rintro ⟨ts', h⟩
    cases ts' with
    | nil => rw [Terms.subst] at h; rw [h]; exists f ⬝ₜ []ₜ
    | cons t' ts' => rw [Terms.subst] at h; rw [h]; exists f ⬝ₜ (t' ∷ₜ ts'); rw [Term.shift, Term.subst, Terms.subst]
theorem Terms.is_shift_iff : (∃ ts', ts = ts'[Subst.shift]ₜₛ) ↔ 0 ∉ ts.vars := match ts with
| []ₜ => by simp [Terms.vars]; exists []ₜ
| t ∷ₜ ts => by
  simp [Terms.vars, not_or]
  rw [←Term.is_shift_iff, ←Terms.is_shift_iff]
  constructor
  · rintro ⟨ts', h⟩
    cases ts' with
    | cons t' ts' =>
      rw [Terms.subst] at h
      injection h with _ h₁ h₂
      subst h₁; subst h₂
      constructor
      · exists t'
      · exists ts'
  · rintro ⟨⟨t', h⟩, ⟨ts', h'⟩⟩
    subst h; subst h'
    exists t' ∷ₜ ts'
    rw [Terms.subst, Term.shift] 
end

def Subst.lift : Subst 𝓛 → Subst 𝓛
| _, 0 => #0
| σ, x + 1 => ↑ₜ(σ x)
prefix:max "⇑ₛ" => Subst.lift

theorem Term.shift_subst_lift : (↑ₜt)[⇑ₛσ]ₜ = ↑ₜ(t[σ]ₜ) := by
  rw [Term.shift, Term.shift, Term.subst_comp, Term.subst_comp]
  apply Term.subst_ext
  funext x
  rfl

theorem Subst.lift_id : ⇑ₛ(Subst.id : Subst 𝓛) = Subst.id := by
  funext x
  cases x <;> simp [Subst.lift, Subst.id, Term.shift, Subst.shift, Term.subst]

theorem Subst.lift_comp : ⇑ₛ(σ₁ ∘ₛ σ₂) = ⇑ₛσ₁ ∘ₛ ⇑ₛσ₂ := by
  funext x
  cases x with
  | zero => rfl
  | succ =>
    simp [Subst.comp, Term.subst]
    rw [Subst.lift]; simp
    rw [Subst.lift]; simp
    rw [Term.shift_subst_lift]



inductive Formula : Language → Type where
| atom : 𝓛.𝓟 n → Terms 𝓛 n → Formula 𝓛
| false : Formula 𝓛
| implies : Formula 𝓛 → Formula 𝓛 → Formula 𝓛
| all : Formula 𝓛 → Formula 𝓛

namespace Formula
  variable (p q : Formula 𝓛)
  
  infix:70 " ⬝ₚ " => atom
  infixr:55 " ⟶ " => implies
  
  instance : Bot (Formula 𝓛) where
    bot := false
  @[reducible] def neg := p ⟶ ⊥
  prefix:58 "~ " => neg
  instance : Top (Formula 𝓛) where
    top := ~ ⊥
  
  @[reducible] def or := ~ p ⟶ q
  infix:56 " ⋁ " => or
  @[reducible] def and := ~ (p ⟶ ~ q)
  infix:57 " ⋀ " => and
  @[reducible] def iff := (p ⟶ q) ⋀ (q ⟶ p)
  infix:55 " ⟷ " => iff
  
  prefix:59 "∀' " =>all
  @[reducible] def exist := ~ ∀' (~ p)
  prefix:59 "∃' " => exist
end Formula

def Formula.free : Formula 𝓛 → Set ℕ
| _ ⬝ₚ ts => ts.vars
| ⊥ => {}
| p ⟶ q => p.free ∪ q.free
| ∀' p => {x | x + 1 ∈ p.free}

def Formula.subst : Formula 𝓛 → Subst 𝓛 → Formula 𝓛
| p ⬝ₚ ts, σ => p ⬝ₚ ts[σ]ₜₛ
| ⊥, _ => ⊥
| p ⟶ q, σ => p.subst σ ⟶ q.subst σ
| ∀' p, σ => ∀' (p.subst ⇑ₛσ)

notation:80 p "[" σ "]ₚ" => Formula.subst p σ

def Formula.shift : Formula 𝓛 → Formula 𝓛 := λ p => p[Subst.shift]ₚ
prefix:max "↑ₚ" => Formula.shift

theorem Formula.subst_ext : σ₁ = σ₂ → p[σ₁]ₚ = p[σ₂]ₚ := by intro h; rw [h]

theorem Formula.subst_id : p[Subst.id]ₚ = p := by
  induction p with
  | atom => simp [Formula.subst, Terms.subst_id]
  | false => rfl
  | implies _ _ ih₁ ih₂ => simp [Formula.subst, ih₁, ih₂]
  | all _ ih => simp [Formula.subst, Subst.lift_id, ih]

theorem Formula.subst_comp : p[σ₁]ₚ[σ₂]ₚ = p[σ₁ ∘ₛ σ₂]ₚ := by
  induction p generalizing σ₁ σ₂ with
  | atom => simp [Formula.subst, Terms.subst_comp]
  | false => rfl
  | implies _ _ ih₁ ih₂ => simp [Formula.subst, ih₁, ih₂]
  | all _ ih => simp [Formula.subst, Terms.subst, Subst.lift_comp, ih]

