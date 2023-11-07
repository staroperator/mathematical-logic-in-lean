import Mathlib.Data.Fin.Basic
import MathematicalLogic.FirstOrder.Syntax
import MathematicalLogic.FirstOrder.Semantics

mutual
inductive BTerm (𝓛 : Language) (m : ℕ) : Type where
| var : Fin m → BTerm 𝓛 m
| func : 𝓛.𝓕 n → BTerms 𝓛 m n → BTerm 𝓛 m
inductive BTerms (𝓛 : Language) (m : ℕ) : ℕ → Type where
| nil : BTerms 𝓛 m 0
| cons : BTerm 𝓛 m → BTerms 𝓛 m n → BTerms 𝓛 m (n + 1)
end

prefix:max "#'" => BTerm.var
infix:70 " ⬝ₜ " => BTerm.func
notation "[]ₜ" => BTerms.nil
infixr:75 " ∷ₜ " => BTerms.cons

mutual
@[simp] def BTerm.size : BTerm 𝓛 m → ℕ
| #'_ => 0
| _ ⬝ₜ ts => ts.size + 1
@[simp] def BTerms.size : BTerms 𝓛 m n → ℕ
| []ₜ => 0
| t ∷ₜ ts => t.size + ts.size + 1
end
termination_by
  BTerm.size t => sizeOf t
  BTerms.size ts => sizeOf ts

instance (priority := high) : SizeOf (BTerm 𝓛 m) := ⟨BTerm.size⟩
instance (priority := high) : SizeOf (BTerms 𝓛 m n) := ⟨BTerms.size⟩
@[simp] theorem BTerm.sizeOf_eq {t : BTerm 𝓛 m} : sizeOf t = t.size := rfl
@[simp] theorem BTerms.sizeOf_eq {ts : BTerms 𝓛 m n} : sizeOf ts = ts.size := rfl

mutual
def BTerm.unbounded : BTerm 𝓛 m → Term 𝓛
| #'x => #x
| f ⬝ₜ ts => f ⬝ₜ ts.unbounded
def BTerms.unbounded : BTerms 𝓛 m n → Terms 𝓛 n
| []ₜ => []ₜ
| t ∷ₜ ts => t.unbounded ∷ₜ ts.unbounded
end

@[simp] theorem BTerm.unbounded_var : (#'x : BTerm 𝓛 m).unbounded = #x := by simp [BTerm.unbounded]
@[simp] theorem BTerm.unbounded_func : (f ⬝ₜ ts : BTerm 𝓛 m).unbounded = f ⬝ₜ ts.unbounded := by simp [BTerm.unbounded]
@[simp] theorem BTerms.unbounded_nil : ([]ₜ : BTerms 𝓛 m 0).unbounded = ([]ₜ : Terms 𝓛 0) := rfl
@[simp] theorem BTerms.unbounded_cons : (t ∷ₜ ts : BTerms 𝓛 m _).unbounded = t.unbounded ∷ₜ ts.unbounded := by simp [BTerms.unbounded]

-- instance : CoeOut (BTerm 𝓛 m) (Term 𝓛) := ⟨BTerm.unbounded⟩
-- instance : CoeOut (BTerms 𝓛 m n) (Terms 𝓛 n) := ⟨BTerms.unbounded⟩

mutual
@[simp] def Term.bound : Term 𝓛 → ℕ
| #x => x + 1
| _ ⬝ₜ ts => ts.bound
@[simp] def Terms.bound : Terms 𝓛 n → ℕ
| []ₜ => 0
| t ∷ₜ ts => max t.bound ts.bound
end

mutual
@[simp] def Term.bounded :
  (t : Term 𝓛) → m ≥ t.bound → BTerm 𝓛 m
| #x, h => #'⟨x, by simp at h; exact h⟩
| f ⬝ₜ ts, h => f ⬝ₜ ts.bounded (by simp at h; exact h)
@[simp] def Terms.bounded :
  (ts : Terms 𝓛 n) → m ≥ ts.bound → BTerms 𝓛 m n
| []ₜ, _ => []ₜ
| t ∷ₜ ts, h => t.bounded (by simp at h; exact h.left) ∷ₜ ts.bounded (by simp at h; exact h.right)
end

mutual
theorem Term.bounded_unbounded {t : Term 𝓛} {h : m ≥ t.bound} :
  (t.bounded h).unbounded = t :=
  match t with
  | #x => by simp
  | f ⬝ₜ ts => by simp; apply Terms.bounded_unbounded
theorem Terms.bounded_unbounded {n : ℕ} {ts : Terms 𝓛 n} {h : m ≥ ts.bound} :
  (ts.bounded h).unbounded = ts :=
  match n, ts with
  | 0, []ₜ => rfl
  | n + 1, t ∷ₜ ts => by
    simp; rw [Term.bounded_unbounded, Terms.bounded_unbounded]; trivial
end



def BSubst (𝓛 m k) := Fin m → BTerm 𝓛 k

mutual
def BTerm.subst : BTerm 𝓛 m → BSubst 𝓛 m k → BTerm 𝓛 k
| #'x, σ => σ x
| f ⬝ₜ ts, σ => f ⬝ₜ ts.subst σ
def BTerms.subst : BTerms 𝓛 m n → BSubst 𝓛 m k → BTerms 𝓛 k n
| []ₜ, σ => []ₜ
| t ∷ₜ ts, σ => t.subst σ ∷ₜ ts.subst σ
end

notation:80 t "[" σ "]ₜ" => BTerm.subst t σ
notation:80 ts "[" σ "]ₜₛ" => BTerms.subst ts σ

@[simp] theorem BTerm.subst_var : (#'x : BTerm 𝓛 m)[σ]ₜ = σ x := by simp [BTerm.subst]
@[simp] theorem BTerm.subst_func : (f ⬝ₜ ts : BTerm 𝓛 m)[σ]ₜ = f ⬝ₜ ts[σ]ₜₛ := by simp [BTerm.subst]
@[simp] theorem BTerms.subst_nil {σ : BSubst 𝓛 m k} : ([]ₜ)[σ]ₜₛ = ([]ₜ : BTerms 𝓛 k 0) := by simp [BTerms.subst]
@[simp] theorem BTerms.subst_cons : (t ∷ₜ ts : BTerms 𝓛 m _)[σ]ₜₛ = t[σ]ₜ ∷ₜ ts[σ]ₜₛ := by simp [BTerms.subst]

def BSubst.id : BSubst 𝓛 m m := λ x => #'x
notation "idₛ" => BSubst.id

mutual
theorem BTerm.subst_id {t : BTerm 𝓛 m} : t[idₛ]ₜ = t :=
  match t with
  | #'x => by simp [BSubst.id]
  | f ⬝ₜ ts => by simp; apply BTerms.subst_id
theorem BTerms.subst_id {ts : BTerms 𝓛 m n} : ts[idₛ]ₜₛ = ts :=
  match ts with
  | []ₜ => rfl
  | t ∷ₜ ts => by simp; rw [BTerm.subst_id, BTerms.subst_id]; trivial
end

def BSubst.shift : BSubst 𝓛 m (m + 1) := λ x => #'(Fin.succ x)
def BTerm.shift (t : BTerm 𝓛 m) := t[BSubst.shift]ₜ
prefix:max "↑ₜ" => BTerm.shift

def BSubst.single (t : BTerm 𝓛 m) : BSubst 𝓛 (m + 1) m := Fin.cons t id
prefix:max "↦ₛ " => BSubst.single

def BSubst.lift (σ : BSubst 𝓛 m k) : BSubst 𝓛 (m + 1) (k + 1) := Fin.cons #'0 (λ x => ↑ₜ(σ x))
prefix:max "⇑ₛ" => BSubst.lift

mutual
theorem BTerm.unbounded_subst_eq
  {t : BTerm 𝓛 m} {σ : BSubst 𝓛 m k} {σ' : Subst 𝓛} :
  (∀ x, (σ x).unbounded = σ' x) → t[σ]ₜ.unbounded = t.unbounded[σ']ₜ :=
  match t with
  | #'x => by intro h; simp [h]
  | f ⬝ₜ ts => by intro h; simp; exact BTerms.unbounded_subst_eq h
theorem BTerms.unbounded_subst_eq
  {ts : BTerms 𝓛 m n} {σ : BSubst 𝓛 m k} {σ' : Subst 𝓛} :
  (∀ x, (σ x).unbounded = σ' x) → ts[σ]ₜₛ.unbounded = ts.unbounded[σ']ₜₛ :=
  match ts with
  | []ₜ => by intro; rfl
  | t ∷ₜ ts => by
    intro h
    simp
    rw [BTerm.unbounded_subst_eq h, BTerms.unbounded_subst_eq h]
    trivial
end

theorem BTerm.unbounded_shift_eq {t : BTerm 𝓛 m} :
  t.shift.unbounded = t.unbounded.shift := by
  simp [BTerm.shift, Term.shift]
  apply BTerm.unbounded_subst_eq
  intro x
  rfl



inductive BFormula (𝓛 : Language) : ℕ → Type where
| atom : 𝓛.𝓟 n → BTerms 𝓛 m n → BFormula 𝓛 m
| fal : BFormula 𝓛 m
| imp : BFormula 𝓛 m → BFormula 𝓛 m → BFormula 𝓛 m
| all : BFormula 𝓛 (m + 1) → BFormula 𝓛 m

infix:70 " ⬝ₚ " => BFormula.atom
instance : FormulaSymbol (BFormula 𝓛 m) := ⟨BFormula.fal, BFormula.imp⟩
prefix:59 "∀ᵇ " => BFormula.all
@[reducible] def BFormula.exists (p : BFormula 𝓛 (m + 1)) := ~ ∀ᵇ (~ p)
prefix:59 "∃ᵇ " => BFormula.exists

@[simp] theorem BFormula.imp_eq : BFormula.imp p q = p ⟶ q := rfl

@[reducible] def Sentence (𝓛) := BFormula 𝓛 0

def BFormula.alls : ∀ {m}, BFormula 𝓛 m → Sentence 𝓛
| 0, p => p
| _ + 1, p => (∀ᵇ p).alls

prefix:59 "∀* " => BFormula.alls

def BFormula.unbounded : BFormula 𝓛 m → Formula 𝓛
| p ⬝ₚ ts => p ⬝ₚ ts.unbounded
| ⊥ => ⊥
| p ⟶ q => p.unbounded ⟶ q.unbounded
| ∀ᵇ p => ∀' p.unbounded

@[simp] theorem BFormula.unbounded_atom : (p ⬝ₚ ts : BFormula 𝓛 m).unbounded = p ⬝ₚ ts.unbounded := rfl
@[simp] theorem BFormula.unbounded_fal : (⊥ : BFormula 𝓛 m).unbounded = ⊥ := rfl
@[simp] theorem BFormula.unbounded_imp : (p ⟶ q : BFormula 𝓛 m).unbounded = p.unbounded ⟶ q.unbounded := rfl
@[simp] theorem BFormula.unbounded_neg : (~ p : BFormula 𝓛 m).unbounded = ~ p.unbounded := rfl
@[simp] theorem BFormula.unbounded_all : (∀ᵇ p).unbounded = ∀' p.unbounded := rfl

-- instance : CoeOut (BFormula 𝓛 m) (Formula 𝓛) := ⟨BFormula.unbounded⟩
instance : Coe (Sentence 𝓛) (Formula 𝓛) := ⟨BFormula.unbounded⟩

@[simp] def Formula.bound : Formula 𝓛 → ℕ
| _ ⬝ₚ ts => ts.bound
| ⊥ => 0
| p ⟶ q => max p.bound q.bound
| ∀' p => p.bound - 1

def Formula.bounded : (p : Formula 𝓛) → m ≥ p.bound → BFormula 𝓛 m
| p ⬝ₚ ts, h => p ⬝ₚ ts.bounded h
| ⊥, _ => ⊥
| p ⟶ q, h => p.bounded (by simp at h; exact h.left) ⟶ q.bounded (by simp at h; exact h.right)
| ∀' p, h => ∀ᵇ p.bounded (by simp at h; exact h)

theorem Formula.bounded_unbounded {p : Formula 𝓛} {h : m ≥ p.bound} :
  (p.bounded h).unbounded = p := by
  induction p generalizing m <;> simp [Formula.bounded]
  case atom => simp [Terms.bounded_unbounded]
  case fal => rfl
  case imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  case all _ ih => simp [ih]

def BFormula.subst : BFormula 𝓛 m → BSubst 𝓛 m k → BFormula 𝓛 k
| p ⬝ₚ ts, σ => p ⬝ₚ ts[σ]ₜₛ
| ⊥, _ => ⊥
| p ⟶ q, σ => p.subst σ ⟶ q.subst σ
| ∀ᵇ p, σ => ∀ᵇ (p.subst ⇑ₛσ)

notation:80 p "[" σ "]ₚ" => BFormula.subst p σ

@[simp] theorem BFormula.subst_atom {σ : BSubst 𝓛 m k} : (p ⬝ₚ ts)[σ]ₚ = p ⬝ₚ ts[σ]ₜₛ := rfl
@[simp] theorem BFormula.subst_fal {σ : BSubst 𝓛 m k} : ⊥[σ]ₚ = ⊥ := rfl
@[simp] theorem BFormula.subst_imp {σ : BSubst 𝓛 m k} : (p ⟶ q)[σ]ₚ = p[σ]ₚ ⟶ q[σ]ₚ := rfl
@[simp] theorem BFormula.subst_neg {σ : BSubst 𝓛 m k} : (~ p)[σ]ₚ = ~ p[σ]ₚ := rfl
@[simp] theorem BFormula.subst_all {σ : BSubst 𝓛 m k} : (∀ᵇ p)[σ]ₚ = ∀ᵇ p[⇑ₛσ]ₚ := rfl

def BFormula.shift (p : BFormula 𝓛 m) := p[BSubst.shift]ₚ
prefix:max "↑ₚ" => BFormula.shift

theorem BFormula.subst_id {p : BFormula 𝓛 m} :
  p[(idₛ : BSubst 𝓛 m m)]ₚ = p := by
  induction p <;> try simp
  case atom => simp [BTerms.subst_id]
  case fal => rfl
  case imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  case all _ ih =>
    conv => rhs; rw [←ih]
    congr
    funext x
    cases x using Fin.cases
    · rfl
    · simp [BSubst.lift, BSubst.id, BTerm.shift, BSubst.shift]

theorem BFormula.unbounded_subst_eq
  {p : BFormula 𝓛 m} {σ : BSubst 𝓛 m k} {σ' : Subst 𝓛} :
  (∀ x, (σ x).unbounded = σ' x) → p[σ]ₚ.unbounded = p.unbounded[σ']ₚ := by
  intro h
  induction p generalizing k σ' <;> try simp
  case atom p ts => simp [BTerms.unbounded_subst_eq h]
  case fal => rfl
  case imp p q ih₁ ih₂ => simp [ih₁ h, ih₂ h]
  case all p ih =>
    apply ih
    intro x
    cases x using Fin.cases
    · rfl
    · simp [BSubst.lift, Subst.lift, BTerm.unbounded_shift_eq, h]

theorem Formula.bounded_subst_single_unbounded
  {p : Formula 𝓛} {h₁ : m + 1 ≥ p.bound}
  {t : Term 𝓛} {h₂ : m ≥ t.bound} :
  (p.bounded h₁)[BSubst.single (t.bounded h₂)]ₚ.unbounded = p[↦ₛ t]ₚ := by
  conv => rhs; rw [←Formula.bounded_unbounded (h := h₁)]
  apply BFormula.unbounded_subst_eq
  intro x
  cases x using Fin.cases
  · simp [BSubst.single, Subst.single, Term.bounded_unbounded]
  · simp [BSubst.single, BSubst.id, Subst.single, Term.bounded_unbounded]

theorem Sentence.unbounded_subst_eq
  {p : Sentence 𝓛} {σ : Subst 𝓛} : p[σ]ₚ = p := by
  conv => rhs; rw [←BFormula.subst_id (p := p)]
  symm
  apply BFormula.unbounded_subst_eq
  apply finZeroElim

theorem Sentence.shift_eq {p : Sentence 𝓛} : ↑ₚ(p : Formula 𝓛) = p :=
  Sentence.unbounded_subst_eq

theorem Sentence.foralls_elim
  {p : BFormula 𝓛 m} {σ : Subst 𝓛} :
  Γ ⊢ ∀* p ⟶ p.unbounded[σ]ₚ := by
  induction' m with m ih generalizing σ
  · rw [Sentence.unbounded_subst_eq]
    exact Proof.identity
  · let σ' := λ x => σ (x + 1)
    apply Proof.mp2 Proof.composition (ih (σ := σ'))
    simp
    have h : ⇑ₛσ' ∘ₛ ↦ₛ (σ 0) = σ
    · funext x
      cases x
      · rfl
      · simp [Subst.comp, Subst.lift, Term.shift_subst_single]
    conv in _[σ]ₚ => rw [←h, ←Formula.subst_comp]
    apply Proof.forall_elim

theorem Sentence.foralls_elim_self {p : BFormula 𝓛 m} :
  Γ ⊢ ∀* p ⟶ p.unbounded := by
  have h := Sentence.foralls_elim (Γ := Γ) (p := p) (σ := Subst.id)
  simp [Formula.subst_id] at h
  exact h



def BAssignment (𝓜 : Structure 𝓛) (m) := Fin m → 𝓜.𝓤

def BAssignment.nil : BAssignment 𝓜 0 := finZeroElim
notation "[]ₐ" => BAssignment.nil

def BAssignment.cons (u : 𝓜.𝓤) (ρ : BAssignment 𝓜 m) : BAssignment 𝓜 (m + 1) := Fin.cons u ρ
infixr:80 " ∷ₐ " => BAssignment.cons

def BAssignment.unbounded (ρ : BAssignment 𝓜 m) : Assignment 𝓜 :=
  λ x => if h : x < m then ρ ⟨x, h⟩ else default

mutual
@[simp] def BTerm.interp : BTerm 𝓛 m → (𝓜 : Structure 𝓛) → BAssignment 𝓜 m → 𝓜.𝓤
| #'x, _, ρ => ρ x
| f ⬝ₜ ts, 𝓜, ρ => 𝓜.𝓕 f (ts.interp 𝓜 ρ)
@[simp] def BTerms.interp : BTerms 𝓛 m n → (𝓜 : Structure 𝓛) → BAssignment 𝓜 m → Vector 𝓜.𝓤 n
| []ₜ, _, _ => []ᵥ
| t ∷ₜ ts, 𝓜, ρ => t.interp 𝓜 ρ ∷ᵥ ts.interp 𝓜 ρ
end

notation:80 "⟦" t "⟧ₜ " 𝓜 ", " ρ:80 => BTerm.interp t 𝓜 ρ
notation:80 "⟦" ts "⟧ₜₛ " 𝓜 ", " ρ:80 => BTerms.interp ts 𝓜 ρ

@[simp] def BFormula.interp : BFormula 𝓛 m → (𝓜 : Structure 𝓛) → BAssignment 𝓜 m → Prop
| p ⬝ₚ ts, 𝓜, ρ => 𝓜.𝓟 p (⟦ ts ⟧ₜₛ 𝓜, ρ)
| ⊥, _, _ => False
| p ⟶ q, 𝓜, ρ => p.interp 𝓜 ρ → q.interp 𝓜 ρ
| ∀ᵇ p, 𝓜, ρ => ∀ u, p.interp 𝓜 (u ∷ₐ ρ)

notation:80 "⟦" p "⟧ₚ" 𝓜 ", " ρ:80 => BFormula.interp p 𝓜 ρ
notation:80 "⟦" p "⟧ₛ" 𝓜:80 => BFormula.interp p 𝓜 []ₐ

mutual
theorem BTerm.unbounded_interp_eq {ρ : BAssignment 𝓜 m} {ρ' : Assignment 𝓜} :
  (∀ x, ρ x = ρ' x) → ⟦ t ⟧ₜ 𝓜, ρ = ⟦ t.unbounded ⟧ₜ 𝓜, ρ' :=
  match t with
  | #'x => by intro h; simp [h]
  | f ⬝ₜ ts => by intro h; simp; rw [BTerms.unbounded_interp_eq h]
theorem BTerms.unbounded_interp_eq {ρ : BAssignment 𝓜 m} {ρ' : Assignment 𝓜} :
  (∀ x, ρ x = ρ' x) → ⟦ ts ⟧ₜₛ 𝓜, ρ = ⟦ ts.unbounded ⟧ₜₛ 𝓜, ρ' :=
  match ts with
  | []ₜ => by intro; rfl
  | t ∷ₜ ts => by
    intro h
    simp
    rw [BTerm.unbounded_interp_eq h, BTerms.unbounded_interp_eq h]
end

theorem BFormula.unbounded_interp_eq {ρ : BAssignment 𝓜 m} {ρ' : Assignment 𝓜} :
  (∀ x, ρ x = ρ' x) → ⟦ p ⟧ₚ 𝓜, ρ = ⟦ p.unbounded ⟧ₚ 𝓜, ρ' := by
  intro h
  induction p generalizing ρ' <;> simp
  case atom => simp [BTerms.unbounded_interp_eq h]
  case imp _ _ ih₁ ih₂ => simp [ih₁ h, ih₂ h]
  case all _ ih =>
    apply forall_congr'
    intro u
    rw [ih]
    intro x
    cases x using Fin.cases
    · rfl
    · simp [BAssignment.cons, Assignment.cons]; apply h

theorem Sentence.unbounded_interp_eq
  {p : Sentence 𝓛} {ρ : Assignment 𝓜} : ⟦ p ⟧ₛ 𝓜 = ⟦ p ⟧ₚ 𝓜, ρ := by
  apply BFormula.unbounded_interp_eq
  apply finZeroElim

theorem BTerm.unbounded_interp {ρ : BAssignment 𝓜 m} :
  ⟦ t ⟧ₜ 𝓜, ρ = ⟦ t.unbounded ⟧ₜ 𝓜, ρ.unbounded := by
  apply BTerm.unbounded_interp_eq
  intro ⟨x, h⟩; simp [BAssignment.unbounded, h]

theorem BTerms.unbounded_interp {ρ : BAssignment 𝓜 m} :
  ⟦ ts ⟧ₜₛ 𝓜, ρ = ⟦ ts.unbounded ⟧ₜₛ 𝓜, ρ.unbounded := by
  apply BTerms.unbounded_interp_eq
  intro ⟨x, h⟩; simp [BAssignment.unbounded, h]

theorem BFormula.unbounded_interp {ρ : BAssignment 𝓜 m} :
  ⟦ p ⟧ₚ 𝓜, ρ = ⟦ p.unbounded ⟧ₚ 𝓜, ρ.unbounded := by
  apply BFormula.unbounded_interp_eq
  intro ⟨x, h⟩; simp [BAssignment.unbounded, h]
