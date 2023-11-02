import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Lattice
import MathematicalLogic.Notation

structure Language where
  𝓕 : ℕ → Type
  𝓟 : ℕ → Type

@[reducible] def Const (𝓛 : Language) := 𝓛.𝓕 0

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
notation "[]ₜ" => Terms.nil
infixr:67 "∷ₜ" => Terms.cons

instance : Coe (Const 𝓛) (Term 𝓛) where
  coe := λ c => c ⬝ₜ []ₜ

mutual
@[simp] def Term.size : Term 𝓛 → ℕ
| #_ => 0
| _ ⬝ₜ ts => ts.size + 1
@[simp] def Terms.size : Terms 𝓛 n → ℕ
| []ₜ => 0
| t ∷ₜ ts => t.size + ts.size + 1
end
termination_by
  Term.size t => sizeOf t
  Terms.size ts => sizeOf ts

instance (priority := high) : SizeOf (Term 𝓛) := ⟨Term.size⟩
instance (priority := high) : SizeOf (Terms 𝓛 n) := ⟨Terms.size⟩
@[simp] theorem Term.sizeOf_eq {t : Term 𝓛} : sizeOf t = t.size := rfl
@[simp] theorem Terms.sizeOf_eq {ts : Terms 𝓛 n} : sizeOf ts = ts.size := rfl

mutual
@[simp] def Term.vars : Term 𝓛 → Set ℕ
| #x => {x}
| _ ⬝ₜ ts => ts.vars
@[simp] def Terms.vars : Terms 𝓛 n → Set ℕ
| []ₜ => {}
| t ∷ₜ ts => t.vars ∪ ts.vars
end



def Subst (𝓛) := ℕ → Term 𝓛

mutual
@[simp] def Term.subst : Term 𝓛 → Subst 𝓛 → Term 𝓛
| #x, σ => σ x
| f ⬝ₜ ts, σ => f ⬝ₜ (ts.subst σ)
@[simp] def Terms.subst : Terms 𝓛 n → Subst 𝓛 → Terms 𝓛 n
| []ₜ, _ => []ₜ
| t ∷ₜ ts, σ => t.subst σ ∷ₜ ts.subst σ
end

notation:80 t "[" σ "]ₜ" => Term.subst t σ
notation:80 ts "[" σ "]ₜₛ" => Terms.subst ts σ

def Subst.id : Subst 𝓛 := λ x => #x

mutual
theorem Term.subst_id : t[Subst.id]ₜ = t :=
  match t with
  | #x => by simp; rfl
  | f ⬝ₜ ts => by simp; rw [Terms.subst_id]
theorem Terms.subst_id : ts[Subst.id]ₜₛ = ts :=
  match ts with
  | []ₜ => by rfl
  | t ∷ₜ ts => by simp; rw [Term.subst_id, Terms.subst_id]; trivial
end

def Subst.comp (σ₁ σ₂ : Subst 𝓛) : Subst 𝓛 := λ x => (σ₁ x)[σ₂]ₜ
infixl:90 " ∘ₛ " => Subst.comp

mutual
theorem Term.subst_comp : t[σ₁]ₜ[σ₂]ₜ = t[σ₁ ∘ₛ σ₂]ₜ :=
  match t with
  | #x => by simp; rfl
  | f ⬝ₜ ts => by simp; rw [Terms.subst_comp]
theorem Terms.subst_comp : ts[σ₁]ₜₛ[σ₂]ₜₛ = ts[σ₁ ∘ₛ σ₂]ₜₛ :=
  match ts with
  | []ₜ => by rfl
  | t ∷ₜ ts => by simp; rw [Term.subst_comp, Terms.subst_comp]; trivial
end

def Subst.single : Term 𝓛 → Subst 𝓛
| t, 0 => t
| _, x + 1 => #x
prefix:max "↦ₛ " => Subst.single

def Subst.shift : Subst 𝓛 := λ x => #(x + 1)
def Term.shift (t : Term 𝓛) := t[Subst.shift]ₜ
prefix:max "↑ₜ" => Term.shift

theorem Term.shift_subst_single : (↑ₜt₁)[↦ₛ t₂]ₜ = t₁ := by
  rw [Term.shift, Term.subst_comp]
  conv => rhs; rw [←Term.subst_id (t := t₁)]

def Subst.lift : Subst 𝓛 → Subst 𝓛
| _, 0 => #0
| σ, x + 1 => ↑ₜ(σ x)
prefix:max "⇑ₛ" => Subst.lift

theorem Term.shift_subst_lift : (↑ₜt)[⇑ₛσ]ₜ = ↑ₜ(t[σ]ₜ) := by
  rw [Term.shift, Term.shift, Term.subst_comp, Term.subst_comp]
  congr

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

mutual
theorem Term.subst_ext_vars {t : Term 𝓛} :
  (∀ x ∈ t.vars, σ₁ x = σ₂ x) → t[σ₁]ₜ = t[σ₂]ₜ :=
  match t with
  | #x => by intro h; simp [h]
  | f ⬝ₜ ts => by
    intro h
    simp at h
    simp
    apply Terms.subst_ext_vars
    exact h
theorem Terms.subst_ext_vars {ts : Terms 𝓛 n} :
  (∀ x ∈ ts.vars, σ₁ x = σ₂ x) → ts[σ₁]ₜₛ = ts[σ₂]ₜₛ :=
  match ts with
  | []ₜ => by intro; rfl
  | t ∷ₜ ts => by
    intro h
    simp at h
    simp
    constructor
    · apply Term.subst_ext_vars; intros; apply h; left; assumption
    · apply Terms.subst_ext_vars; intros; apply h; right; assumption
end

mutual
theorem Term.vars_of_subst : t[σ]ₜ.vars = ⋃ x ∈ t.vars, (σ x).vars :=
  match t with
  | #x => by simp
  | f ⬝ₜ ts => by simp; rw [Terms.vars_of_subst]
theorem Terms.vars_of_subst : ts[σ]ₜₛ.vars = ⋃ x ∈ ts.vars, (σ x).vars :=
  match ts with
  | []ₜ => by simp
  | t ∷ₜ ts => by
    conv => lhs; simp
    conv => rhs; rw [Terms.vars]
    rw [Term.vars_of_subst, Terms.vars_of_subst, Set.biUnion_union]
end

theorem Term.is_shift_iff : (∃ t', t = ↑ₜt') ↔ 0 ∉ t.vars := by
  constructor
  · rintro ⟨t, h⟩
    subst h
    intro h
    simp [Term.shift, Term.vars_of_subst] at h
    rcases h with ⟨x, ⟨_, h⟩⟩
    contradiction
  · intro h
    exists t[↦ₛ #0]ₜ
    rw [Term.shift, Term.subst_comp]
    conv => lhs; rw [←Term.subst_id (t := t)]
    apply Term.subst_ext_vars
    intros x h₁
    cases x
    · contradiction
    · simp [Subst.id, Subst.comp, Subst.shift, Subst.single]



inductive Formula : Language → Type where
| atom : 𝓛.𝓟 n → Terms 𝓛 n → Formula 𝓛
| false : Formula 𝓛
| imp : Formula 𝓛 → Formula 𝓛 → Formula 𝓛
| all : Formula 𝓛 → Formula 𝓛

infix:70 " ⬝ₚ " => Formula.atom
instance : Bot (Formula 𝓛) := ⟨Formula.false⟩
instance : ImpSymbol (Formula 𝓛) := ⟨Formula.imp⟩
instance : NotSymbol (Formula 𝓛) := ⟨λ p => p ⟶ ⊥⟩
instance : Top (Formula 𝓛) := ⟨~ ⊥⟩
instance : OrSymbol (Formula 𝓛) := ⟨λ p q => ~ p ⟶ q⟩
instance : AndSymbol (Formula 𝓛) := ⟨λ p q => ~ (p ⟶ ~ q)⟩
instance : IffSymbol (Formula 𝓛) := ⟨λ p q => (p ⟶ q) ⋀ (q ⟶ p)⟩
instance : ForallSymbol (Formula 𝓛) := ⟨Formula.all⟩
instance : ExistsSymbol (Formula 𝓛) := ⟨λ p => ~ ∀' (~ p)⟩

@[simp] theorem Formula.imp_eq : Formula.imp p q = p ⟶ q := rfl
@[simp] theorem Formula.all_eq : Formula.all p = ∀' p := rfl

@[simp] def Formula.free : Formula 𝓛 → Set ℕ
| _ ⬝ₚ ts => ts.vars
| ⊥ => {}
| p ⟶ q => p.free ∪ q.free
| ∀' p => { x | x + 1 ∈ p.free }

@[simp] def Formula.subst : Formula 𝓛 → Subst 𝓛 → Formula 𝓛
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
  | atom => simp [Terms.subst_id]
  | false => rfl
  | imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | all _ ih => simp [Subst.lift_id, ih]

theorem Formula.subst_comp : p[σ₁]ₚ[σ₂]ₚ = p[σ₁ ∘ₛ σ₂]ₚ := by
  induction p generalizing σ₁ σ₂ with
  | atom => simp [Terms.subst_comp]
  | false => rfl
  | imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | all _ ih => simp [Subst.lift_comp, ih]

theorem Formula.shift_subst_single : (↑ₚp)[↦ₛ t₂]ₚ = p := by
  rw [Formula.shift, Formula.subst_comp]
  conv => rhs; rw [←Formula.subst_id (p := p)]

theorem Formula.subst_ext_free {p : Formula 𝓛} :
  (∀ x ∈ p.free, σ₁ x = σ₂ x) → p[σ₁]ₚ = p[σ₂]ₚ := by
  intro h
  induction p generalizing σ₁ σ₂ with
  | atom => simp at h; simp [Terms.subst_ext_vars h]
  | false => rfl
  | imp _ _ ih₁ ih₂ =>
    simp at h; simp; rw [ih₁, ih₂]
    · intros; apply h; right; assumption
    · intros; apply h; left; assumption
  | all _ ih =>
    simp at h; simp; rw [ih]
    intros x h₁
    cases x
    · rfl
    · simp [Subst.lift]; congr; apply h; exact h₁

theorem Formula.free_of_subst : p[σ]ₚ.free = ⋃ x ∈ p.free, (σ x).vars := by
  induction p generalizing σ with
  | atom => simp [Terms.vars_of_subst]
  | false => simp
  | imp p q ih₁ ih₂ =>
    conv => lhs; simp
    conv => rhs; rw [Formula.free]
    rw [ih₁, ih₂, Set.biUnion_union]
  | all p ih =>
    conv => lhs; simp [ih]
    conv => rhs; rw [Formula.free]
    apply Set.ext
    intro x; simp
    constructor
    · rintro ⟨y, ⟨h₁, h₂⟩⟩
      cases y with
      | zero => contradiction
      | succ y =>
        simp [Subst.lift, Term.shift, Term.vars_of_subst] at h₂
        rcases h₂ with ⟨z, ⟨h₂, h₃⟩⟩
        simp [Subst.shift] at h₃
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
    simp [Formula.shift, Formula.free_of_subst] at h
    rcases h with ⟨x, ⟨_, h⟩⟩
    contradiction
  · intro h
    exists p[↦ₛ #0]ₚ
    rw [Formula.shift, Formula.subst_comp]
    conv => lhs; rw [←Formula.subst_id (p := p)]
    apply Formula.subst_ext_free
    intros x h₁
    cases x
    · contradiction
    · simp [Subst.id, Subst.comp, Subst.shift, Subst.single]
