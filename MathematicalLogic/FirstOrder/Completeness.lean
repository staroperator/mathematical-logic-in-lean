-- import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Perm
import Mathlib.Data.List.Sort
import MathematicalLogic.FirstOrder.Proof
import MathematicalLogic.FirstOrder.Semantics



@[reducible]
def Language.addConsts (𝓛 : Language) (𝓒 : Type) : Language where
  𝓕 := λ
       | 0 => 𝓛.𝓕 0 ⊕ 𝓒
       | n + 1 => 𝓛.𝓕 (n + 1)
  𝓟 := 𝓛.𝓟

local infix:70 " ⊎ " => Language.addConsts

mutual
def Term.injConsts : Term 𝓛 → Term (𝓛 ⊎ 𝓒)
| #x => #x
| Term.func (n := 0) f ([]ₜ) => Sum.inl f ⬝ₜ []ₜ
| Term.func (n := n + 1) f ts => f ⬝ₜ ts.injConsts
def Terms.injConsts : Terms 𝓛 n → Terms (𝓛 ⊎ 𝓒) n
| []ₜ => []ₜ
| t ∷ₜ ts => t.injConsts ∷ₜ ts.injConsts
end
termination_by
  Term.injConsts t => t.size
  Terms.injConsts ts => ts.size

local notation "⌈" t "⌉ₜ" => Term.injConsts t
local notation "⌈" ts "⌉ₜₛ" => Terms.injConsts ts

def Formula.injConsts : Formula 𝓛 → Formula (𝓛 ⊎ 𝓒)
| p ⬝ₚ ts => p ⬝ₚ ts.injConsts
| ⊥ => ⊥
| p ⟶ q => p.injConsts ⟶ q.injConsts
| ∀' p => ∀' p.injConsts

local notation "⌈" p "⌉ₚ" => Formula.injConsts p

def Formulas.injConsts (Γ : Formulas 𝓛) : Formulas (𝓛 ⊎ 𝓒) :=
  { ⌈p⌉ₚ | p ∈ Γ }

local notation "⌈" Γ "⌉ₚₛ" => Formulas.injConsts Γ

mutual
def Term.eraseConsts : Term (𝓛 ⊎ 𝓒) → ℕ → Term 𝓛
| #x, _ => #x
| Term.func (n := 0) (Sum.inl f) ([]ₜ), _ => f ⬝ₜ []ₜ
| Term.func (n := 0) (Sum.inr _) ([]ₜ), x => #x
| Term.func (n := n + 1) f ts, x => f ⬝ₜ ts.eraseConsts x
def Terms.eraseConsts : Terms (𝓛 ⊎ 𝓒) n → ℕ → Terms 𝓛 n
| []ₜ, _ => []ₜ
| t ∷ₜ ts, x => t.eraseConsts x ∷ₜ ts.eraseConsts x
end
termination_by
  Term.eraseConsts t _ => t.size
  Terms.eraseConsts ts _ => ts.size

local notation "⌊" t "⌋ₜ" => Term.eraseConsts t
local notation "⌊" ts "⌋ₜₛ" => Terms.eraseConsts ts

def Formula.eraseConsts : Formula (𝓛 ⊎ 𝓒) → ℕ → Formula 𝓛
| p ⬝ₚ ts, x => p ⬝ₚ (⌊ts⌋ₜₛ x)
| ⊥, _ => ⊥
| p ⟶ q, x => p.eraseConsts x ⟶ q.eraseConsts x
| ∀' p, x => ∀' (p.eraseConsts (x + 1))

local notation "⌊" p "⌋ₚ" => Formula.eraseConsts p

mutual
lemma Term.erase_inj : ⌊(⌈t⌉ₜ : Term (𝓛 ⊎ 𝓒))⌋ₜ x = t :=
  match t with
  | #x => by simp [Term.injConsts, Term.eraseConsts]
  | Term.func (n := 0) f ([]ₜ) => by rfl
  | Term.func (n := n + 1) f ts => by
    simp [Term.injConsts, Term.eraseConsts]
    rw [Terms.erase_inj]
lemma Terms.erase_inj : ⌊(⌈ts⌉ₜₛ : Terms (𝓛 ⊎ 𝓒) n)⌋ₜₛ x = ts :=
  match ts with
  | []ₜ => rfl
  | t ∷ₜ ts => by
    simp [Terms.injConsts, Terms.eraseConsts]
    rw [Term.erase_inj, Terms.erase_inj]
    trivial
end
termination_by
  Term.erase_inj => t.size
  Terms.erase_inj => ts.size

lemma Formula.erase_inj : ⌊(⌈p⌉ₚ : Formula (𝓛 ⊎ 𝓒))⌋ₚ x = p := by
  induction p generalizing x with
  | atom => simp [Formula.injConsts, Formula.eraseConsts, Terms.erase_inj]
  | false => rfl
  | implies _ _ ih₁ ih₂ => simp [Formula.injConsts, Formula.eraseConsts, ih₁, ih₂]
  | all _ ih => simp [Formula.injConsts, Formula.eraseConsts, ih]

mutual
lemma Term.erase_swap_subst :
  (∀ z, σ₂ z = ⌊σ₁ z⌋ₜ x) → σ₂ y = #x → ⌊t[σ₁]ₜ⌋ₜ x = (⌊t⌋ₜ y)[σ₂]ₜ :=
  match t with
  | #z => by
    intro h₁ _; simp [Term.eraseConsts, h₁]
  | Term.func (n := 0) (Sum.inl f) ([]ₜ) => by
    intros; simp [Term.eraseConsts]
  | Term.func (n := 0) (Sum.inr c) ([]ₜ) => by
    intros _ h₂; simp [Term.eraseConsts, h₂]
  | Term.func (n := n + 1) f ts => by
    intros h₁ h₂; simp [Term.eraseConsts]; rw [Terms.erase_swap_subst h₁ h₂]
lemma Terms.erase_swap_subst :
  (∀ z, σ₂ z = ⌊σ₁ z⌋ₜ x) → σ₂ y = #x → ⌊ts[σ₁]ₜₛ⌋ₜₛ x = (⌊ts⌋ₜₛ y)[σ₂]ₜₛ :=
  match ts with
  | []ₜ => by intros; rfl
  | t ∷ₜ ts => by
    intros h₁ h₂
    simp [Terms.eraseConsts]
    rw [Term.erase_swap_subst h₁ h₂, Terms.erase_swap_subst h₁ h₂]
    trivial
end
termination_by
  Term.erase_swap_subst => t.size
  Terms.erase_swap_subst => ts.size

lemma Formula.erase_swap_subst :
  (∀ z, σ₂ z = ⌊σ₁ z⌋ₜ x) → σ₂ y = #x → ⌊p[σ₁]ₚ⌋ₚ x = (⌊p⌋ₚ y)[σ₂]ₚ := by
  intros h₁ h₂
  induction p generalizing σ₁ σ₂ x y <;> simp [Formula.eraseConsts]
  case atom => simp [Terms.erase_swap_subst h₁ h₂]
  case implies _ _ ih₁ ih₂ => simp [ih₁ h₁ h₂, ih₂ h₁ h₂]
  case all _ ih =>
    rw [ih]
    · intro z; cases z
      · rfl
      · simp [Subst.lift, Term.shift]
        rw [h₁, Term.erase_swap_subst]
        · simp [Subst.shift, Term.eraseConsts]
        · rfl
    · simp [Subst.lift, h₂, Term.shift, Subst.shift]

lemma erase_keeps_axioms {p : Formula _} :
  p ∈ Axioms (𝓛 ⊎ 𝓒) → ⌊p⌋ₚ x ∈ Axioms 𝓛 := by
  intro h
  induction h generalizing x <;> simp [Formula.eraseConsts] <;> try constructor
  case a4 p t =>
    rw [Formula.erase_swap_subst (σ₂ := ↦ₛ (⌊t⌋ₜ x))]
    · apply Axioms.a4
    · intro z; cases z
      · rfl
      · simp [Subst.single, Term.eraseConsts]
    · rfl
  case a5 p =>
    rw [Formula.shift, Formula.erase_swap_subst (σ₂ := Subst.shift)]
    · apply Axioms.a5
    · intro z; simp [Subst.shift, Term.eraseConsts]
    · rfl
  case a7 ih =>
    apply ih

lemma erase_keeps_proof : ⌈Γ⌉ₚₛ ⊢ p → Γ ⊢ ⌊p⌋ₚ x := by
  intro h
  induction h with
  | assumption h =>
    rcases h with ⟨p', ⟨h₁, h₂⟩⟩
    subst h₂
    simp [Formula.erase_inj]
    apply Proof.assumption
    exact h₁
  | axioms h =>
    apply Proof.axioms
    apply erase_keeps_axioms
    exact h
  | mp _ _ ih₁ ih₂ =>
    apply Proof.mp
    · exact ih₁
    · exact ih₂

theorem consts_keeps_consistency :
  Consistent Γ → Consistent (𝓛 := _ ⊎ 𝓒) (⌈Γ⌉ₚₛ) := by
  intros h h₁
  apply erase_keeps_proof (x := 0) at h₁
  apply h
  exact h₁

def Model.eraseConsts (𝓜 : Model (𝓛 ⊎ 𝓒)) : Model 𝓛 where
  𝓤 := 𝓜.𝓤
  𝓕 := @λ n f =>
    match n with
    | 0 => 𝓜.𝓕 (Sum.inl f)
    | _ + 1 => 𝓜.𝓕 f
  𝓟 := 𝓜.𝓟

local notation "⌊" 𝓜 "⌋ₘ" => Model.eraseConsts 𝓜

mutual
lemma Term.interp_erase : ⟦ t ⟧ₜ ⌊𝓜⌋ₘ, ρ = ⟦ ⌈t⌉ₜ ⟧ₜ 𝓜, ρ :=
  match t with
  | #x => by
    simp [Term.injConsts, Term.interp]
  | Term.func (n := 0) f ([]ₜ) => rfl
  | Term.func (n := n + 1) f ts => by
    simp [Term.injConsts, Term.interp]
    rw [Terms.interp_erase]
    rfl
lemma Terms.interp_erase : ⟦ ts ⟧ₜₛ ⌊𝓜⌋ₘ, ρ = ⟦ ⌈ts⌉ₜₛ ⟧ₜₛ 𝓜, ρ :=
  match ts with
  | []ₜ => rfl
  | t ∷ₜ ts => by
    simp [Terms.injConsts, Terms.interp]
    rw [Term.interp_erase, Terms.interp_erase]
end
termination_by
  Term.interp_erase => t.size
  Terms.interp_erase => ts.size

lemma Formula.interp_erase :
  ⟦ p ⟧ₚ ⌊𝓜⌋ₘ, ρ = ⟦ ⌈p⌉ₚ ⟧ₚ 𝓜, ρ := by
  induction p generalizing ρ with
  | atom => simp [Formula.injConsts, Formula.interp, Terms.interp_erase]; rfl
  | false => rfl
  | implies _ _ ih₁ ih₂ => simp [Formula.injConsts, Formula.interp, ih₁, ih₂]
  | all _ ih =>
    rw [Formula.injConsts, Formula.interp]
    apply forall_congr
    intro
    rw [ih]
    rfl

theorem consts_keeps_satisfiability :
  Satisfiable.{u} (𝓛 := 𝓛 ⊎ 𝓒) (⌈Γ⌉ₚₛ) → Satisfiable.{u} Γ := by
  rintro ⟨𝓜, ⟨ρ, h⟩⟩
  exists 𝓜.eraseConsts
  exists ρ
  intros p h₁
  rw [Formula.interp_erase]
  apply h
  exists p



mutual
def Term.consts : Term 𝓛 → Set (Const 𝓛)
| #_ => {}
| Term.func (n := 0) c ([]ₜ) => {c}
| Term.func (n := n + 1) _ ts => ts.consts
def Terms.consts : Terms 𝓛 n → Set (Const 𝓛)
| []ₜ => {}
| t ∷ₜ ts => t.consts ∪ ts.consts
end
termination_by
  Term.consts t => t.size
  Terms.consts ts => ts.size

def Formula.consts : Formula 𝓛 → Set (Const 𝓛)
| _ ⬝ₚ ts => ts.consts
| ⊥ => {}
| p ⟶ q => p.consts ∪ q.consts
| ∀' p => p.consts

mutual
lemma Term.consts_of_subst :
  t[σ]ₜ.consts = t.consts ∪ ⋃ x ∈ t.vars, (σ x).consts :=
  match t with
  | #x => by simp [Term.consts]
  | Term.func (n := 0) c ([]ₜ) => by simp
  | Term.func (n := n + 1) f ts => by
    simp [Term.consts]
    rw [Terms.consts_of_subst]
lemma Terms.consts_of_subst :
  ts[σ]ₜₛ.consts = ts.consts ∪ ⋃ x ∈ ts.vars, (σ x).consts :=
  match ts with
  | []ₜ => by simp
  | t ∷ₜ ts => by
    conv => lhs; simp [Terms.consts]
    conv => rhs; rw [Terms.consts, Terms.vars, Set.biUnion_union]
    rw [Term.consts_of_subst, Terms.consts_of_subst]
    simp [Set.union_assoc, Set.union_left_comm]
end
termination_by
  Term.consts_of_subst => t.size
  Terms.consts_of_subst => ts.size

lemma Formula.consts_of_subst :
  p[σ]ₚ.consts = p.consts ∪ ⋃ x ∈ p.free, (σ x).consts := by
  induction p generalizing σ
    <;> (conv => lhs; simp [Formula.consts])
    <;> (conv => rhs; rw [Formula.consts, Formula.free]; try rw [Set.biUnion_union])
  case atom => simp [Terms.consts_of_subst]
  case false => simp
  case implies _ _ ih₁ ih₂ => simp [ih₁, ih₂, Set.union_assoc, Set.union_left_comm]
  case all _ ih =>
    simp [ih]
    congr
    apply Set.ext
    intro x; simp
    constructor
    · rintro ⟨y, h₁, h₂⟩
      cases' y with y
      · simp [Subst.lift, Term.consts] at h₂
      · simp [Subst.lift, Term.shift, Term.consts_of_subst] at h₂
        rcases h₂ with h₂ | ⟨z, _, h₂⟩
        · exists y
        · simp [Subst.shift, Term.consts] at h₂
    · rintro ⟨y, h₁, h₂⟩
      exists y + 1
      constructor
      · exact h₁
      · simp [Subst.lift, Term.shift, Term.consts_of_subst]
        left
        exact h₂

local instance : Coe (Const 𝓛) (Term 𝓛) where
  coe := λ c => c ⬝ₜ []ₜ

mutual
def Term.substConst [DecidableEq (Const 𝓛)] : Term 𝓛 → Const 𝓛 → ℕ → Term 𝓛
| #x, _, y =>
  if x < y then #x else #(x + 1)
| Term.func (n := 0) c ([]ₜ), c', x =>
  if c = c' then #x else c
| Term.func (n := n + 1) f ts, c, x => f ⬝ₜ ts.substConst c x
def Terms.substConst [DecidableEq (Const 𝓛)] : Terms 𝓛 n → Const 𝓛 → ℕ → Terms 𝓛 n
| []ₜ, _, _ => []ₜ
| t ∷ₜ ts, c, x => t.substConst c x ∷ₜ ts.substConst c x
end
termination_by
  Term.substConst t _ _ => t.size
  Terms.substConst ts _ _ => ts.size

local notation t "[" c " ↦ᶜ " x "]ₜ" => Term.substConst t c x
local notation ts "[" c " ↦ᶜ " x "]ₜₛ" => Terms.substConst ts c x

def Formula.substConst [DecidableEq (Const 𝓛)] : Formula 𝓛 → Const 𝓛 → ℕ → Formula 𝓛
| p ⬝ₚ ts, c, x => p ⬝ₚ ts[c ↦ᶜ x]ₜₛ
| ⊥, _, _ => ⊥
| p ⟶ q, c, x => p.substConst c x ⟶ q.substConst c x
| ∀' p, c, x => ∀' (p.substConst c (x + 1))

local notation p "[" c " ↦ᶜ " x "]ₚ" => Formula.substConst p c x

def Subst.shift_since (x : ℕ) : Subst 𝓛 := λ y => if y < x then #y else #(y + 1)

mutual
lemma Term.subst_const_of_non_const_aux [DecidableEq (Const 𝓛)] {t : Term 𝓛} :
  c ∉ t.consts → t[c ↦ᶜ x]ₜ = t[Subst.shift_since x]ₜ :=
  match t with
  | #y => by intro; simp [Term.substConst, Subst.shift_since]
  | Term.func (n := 0) c' ([]ₜ) => by
    intro h
    simp [Term.consts] at h
    simp [Term.substConst, Ne.symm h]
  | Term.func (n := n + 1) f ts => by
    intro h
    simp [Term.consts] at h
    simp [Term.substConst]
    rw [Terms.subst_const_of_non_const_aux h]
lemma Terms.subst_const_of_non_const_aux [DecidableEq (Const 𝓛)] {ts : Terms 𝓛 n} :
  c ∉ ts.consts → ts[c ↦ᶜ x]ₜₛ = ts[Subst.shift_since x]ₜₛ :=
  match ts with
  | []ₜ => by intro; rfl
  | t ∷ₜ ts => by
    intro h
    simp [Terms.consts, not_or] at h
    rcases h with ⟨h₁, h₂⟩
    simp [Terms.substConst]
    rw [Term.subst_const_of_non_const_aux h₁, Terms.subst_const_of_non_const_aux h₂]
    trivial
end
termination_by
  Term.subst_const_of_non_const_aux => t.size
  Terms.subst_const_of_non_const_aux => ts.size

lemma Formula.subst_const_of_non_const_aux [DecidableEq (Const 𝓛)] {p : Formula 𝓛} :
  c ∉ p.consts → p[c ↦ᶜ x]ₚ = p[Subst.shift_since x]ₚ := by
  intro h
  induction p generalizing x <;> simp [Formula.substConst]
  case atom => simp [Terms.subst_const_of_non_const_aux h]
  case implies _ _ ih₁ ih₂ =>
    simp [Formula.consts, not_or] at h
    rcases h with ⟨h₁, h₂⟩
    rw [ih₁ h₁, ih₂ h₂]
    trivial
  case all _ ih =>
    rw [ih h]
    congr
    funext y
    cases y with
    | zero => simp [Subst.lift, Subst.shift_since]
    | succ y =>
      simp [Subst.lift, Subst.shift_since]
      by_cases h : y < x
      · simp [h, Nat.succ_lt_succ h, Term.shift, Subst.shift]
      · simp [h, mt Nat.lt_of_succ_lt_succ h, Term.shift, Subst.shift]

lemma Formula.subst_const_of_non_const [DecidableEq (Const 𝓛)] {p : Formula 𝓛} :
  c ∉ p.consts → p[c ↦ᶜ 0]ₚ = ↑ₚp :=
  Formula.subst_const_of_non_const_aux

mutual
lemma Term.subst_const_swap_subst [DecidableEq (Const 𝓛)] {t : Term 𝓛} :
  (∀ z, σ₂ (if z < y then z else z + 1) = (σ₁ z)[c ↦ᶜ x]ₜ) →
  σ₂ y = #x → t[σ₁]ₜ[c ↦ᶜ x]ₜ = t[c ↦ᶜ y]ₜ[σ₂]ₜ :=
  match t with
  | #z => by
    intros h₁ _
    simp [Term.substConst, ←h₁]
    by_cases h : z < y <;> simp [h]
  | Term.func (n := 0) c' ([]ₜ) => by
    intros _ h₂
    simp [Term.substConst]
    by_cases h : c' = c <;> simp [h, h₂]
  | Term.func (n := n + 1) f ts => by
    intros h₁ h₂
    simp [Term.substConst]
    rw [Terms.subst_const_swap_subst h₁ h₂]
lemma Terms.subst_const_swap_subst [DecidableEq (Const 𝓛)] {ts : Terms 𝓛 n} :
  (∀ z, σ₂ (if z < y then z else z + 1) = (σ₁ z)[c ↦ᶜ x]ₜ) →
  σ₂ y = #x → ts[σ₁]ₜₛ[c ↦ᶜ x]ₜₛ = ts[c ↦ᶜ y]ₜₛ[σ₂]ₜₛ :=
  match ts with
  | []ₜ => by intros; rfl
  | t ∷ₜ ts => by
    intros h₁ h₂
    simp [Terms.substConst]
    rw [Term.subst_const_swap_subst h₁ h₂, Terms.subst_const_swap_subst h₁ h₂]
    trivial
end
termination_by
  Term.subst_const_swap_subst => t.size
  Terms.subst_const_swap_subst => ts.size

lemma Formula.subst_const_swap_subst [DecidableEq (Const 𝓛)] {p : Formula 𝓛} :
  (∀ z, σ₂ (if z < y then z else z + 1) = (σ₁ z)[c ↦ᶜ x]ₜ) →
  σ₂ y = #x → p[σ₁]ₚ[c ↦ᶜ x]ₚ = p[c ↦ᶜ y]ₚ[σ₂]ₚ := by
  intros h₁ h₂
  induction p generalizing σ₁ σ₂ x y <;> simp [Formula.substConst]
  case atom => simp [Terms.subst_const_swap_subst h₁ h₂]
  case implies _ _ ih₁ ih₂ => simp [ih₁ h₁ h₂, ih₂ h₁ h₂]
  case all _ ih =>
    rw [ih]
    · intro z
      cases z with
      | zero => simp [Subst.lift, Term.substConst]
      | succ z =>
        replace h₁ := h₁ z
        by_cases h : z < y
        · simp [h] at h₁
          simp [Nat.succ_lt_succ h, Subst.lift, h₁, Term.shift]
          rw [Term.subst_const_swap_subst]
          · intro z'; simp [Subst.shift, Term.substConst]
            by_cases h : z' < x <;> simp [h]
          · rfl
        · simp [h] at h₁
          simp [mt Nat.lt_of_succ_lt_succ h, Subst.lift, h₁, Term.shift]
          rw [Term.subst_const_swap_subst]
          · intro z'; simp [Subst.shift, Term.substConst]
            by_cases h : z' < x <;> simp [h]
          · rfl
    · simp [Subst.lift, h₂, Term.shift, Subst.shift]

theorem subst_const_keeps_axioms [DecidableEq (Const 𝓛)] :
  p ∈ Axioms 𝓛 → p[c ↦ᶜ x]ₚ ∈ Axioms 𝓛 := by
  intro h
  induction h generalizing x <;> simp [Formula.substConst] <;> try constructor
  case a4 p t =>
    rw [Formula.subst_const_swap_subst (σ₂ := ↦ₛ (t[c ↦ᶜ x]ₜ))]
    · apply Axioms.a4
    · intro z
      cases z with
      | zero => simp [Subst.single]
      | succ z =>
        by_cases h : z < x
        · simp [h, Nat.succ_lt_succ h, Subst.single, Term.substConst]
        · simp [h, mt Nat.lt_of_succ_lt_succ h, Subst.single, Term.substConst]
    · rfl
  case a5 p =>
    rw [Formula.shift, Formula.subst_const_swap_subst (σ₂ := Subst.shift)]
    · apply Axioms.a5
    · intro z
      by_cases h : z < x <;> simp [h, Subst.shift, Term.substConst]
    · rfl
  case a7 ih =>
    apply ih

theorem subst_const_keeps_proof [DecidableEq (Const 𝓛)] {p : Formula 𝓛} :
  (∀ p ∈ Γ, c ∉ p.consts) → Γ ⊢ p → Γ ⊢ ∀' p[c ↦ᶜ 0]ₚ := by
  intros h₁ h
  induction h with
  | assumption h =>
    rw [Formula.subst_const_of_non_const (h₁ _ h)]
    apply Proof.mp (Proof.axioms Axioms.a5)
    apply Proof.assumption
    exact h
  | axioms h =>
    apply Proof.axioms
    apply Axioms.a7
    apply subst_const_keeps_axioms
    exact h
  | mp _ _ ih₁ ih₂ =>
    apply Proof.mp2 (Proof.axioms Axioms.a6)
    · exact ih₁
    · exact ih₂

theorem const_generalization {c : Const 𝓛} :
  (∀ p ∈ Γ, c ∉ p.consts) → c ∉ p.consts → Γ ⊢ p[↦ₛ c]ₚ → Γ ⊢ ∀' p := by
  have := Classical.decEq
  intros h₁ h₂ h₃
  apply subst_const_keeps_proof h₁ at h₃
  rw [Formula.subst_const_swap_subst (σ₂ := (↦ₛ #0))] at h₃
  · rw [Formula.subst_const_of_non_const h₂, Formula.shift_subst_single] at h₃
    exact h₃
  · intro z
    cases z with
    | zero => simp [Subst.single, Term.substConst]
    | succ z => simp [Subst.single, Term.substConst]
  · rfl



def Language.witnessAcc (𝓛 : Language) : ℕ → Type
| 0 => Empty
| n + 1 => 𝓛.witnessAcc n ⊕ Formula (𝓛 ⊎ 𝓛.witnessAcc n)

def Language.witnessNth (𝓛 : Language) (n : ℕ) : Type
  := Formula (𝓛 ⊎ 𝓛.witnessAcc n)

def Language.addWitnessNth (𝓛 n)
  := 𝓛 ⊎ 𝓛.witnessAcc n
local instance : Pow Language ℕ where
  pow := Language.addWitnessNth

def Language.witnessOmega (𝓛 : Language) : Type
  := Σ n, 𝓛.witnessNth n
@[reducible] def Language.addWitness (𝓛 : Language)
  := 𝓛 ⊎ 𝓛.witnessOmega
local postfix:max "*" => Language.addWitness

def injOmegaWitness {𝓛 : Language} : {n : ℕ} → 𝓛.witnessAcc n → 𝓛.witnessOmega
| _ + 1, Sum.inl c => injOmegaWitness c
| n + 1, Sum.inr c => ⟨n, c⟩

mutual
def Term.injOmega {n : ℕ} : Term (𝓛^n) → Term 𝓛*
| #x => #x
| Term.func (n := 0) (Sum.inl f) ([]ₜ) => Sum.inl f ⬝ₜ []ₜ
| Term.func (n := 0) (Sum.inr c) ([]ₜ) => Sum.inr (injOmegaWitness c) ⬝ₜ []ₜ
| Term.func (n := n + 1) f ts => f ⬝ₜ ts.injOmega
def Terms.injOmega {n : ℕ} : Terms (𝓛^n) m → Terms 𝓛* m
| []ₜ => []ₜ
| t ∷ₜ ts => t.injOmega ∷ₜ ts.injOmega
end
termination_by
  Term.injOmega t => t.size
  Terms.injOmega ts => ts.size

def Formula.injOmega {n : ℕ} : Formula (𝓛^n) → Formula 𝓛*
| p ⬝ₚ ts => p ⬝ₚ ts.injOmega
| ⊥ => ⊥
| p ⟶ q => p.injOmega ⟶ q.injOmega
| ∀' p => ∀' (p.injOmega)

mutual
def Term.level : Term 𝓛* → ℕ
| #_ => 0
| Term.func (n := 0) (Sum.inl _) ([]ₜ) => 0
| Term.func (n := 0) (Sum.inr c) ([]ₜ) => c.fst + 1
| Term.func (n := n + 1) _ ts => ts.level
def Terms.level : Terms 𝓛* n → ℕ
| []ₜ => 0
| t ∷ₜ ts => max t.level ts.level
end
termination_by
  Term.level t => t.size
  Terms.level ts => ts.size

def Formula.level : Formula 𝓛* → ℕ
| _ ⬝ₚ ts => ts.level
| ⊥ => 0
| p ⟶ q => max p.level q.level
| ∀' p => p.level

mutual
lemma Term.const_less_than_level {t : Term 𝓛*} :
  Sum.inr ⟨k, q⟩ ∈ t.consts → k < t.level :=
  match t with
  | #_ => by simp [Term.consts]
  | Term.func (n := 0) (Sum.inl _) ([]ₜ) => by simp [Term.consts]
  | Term.func (n := 0) (Sum.inr ⟨k, _⟩) ([]ₜ) => by
    intro h
    simp [Term.consts] at h
    injection h with h₁ h₂
    subst h₁ h₂
    simp [Term.level]
  | Term.func (n := n + 1) _ ts => by
    intro h
    simp [Term.level]
    apply Terms.const_less_than_level
    simp [Term.consts] at h
    exact h
lemma Terms.const_less_than_level {ts : Terms 𝓛* n} :
  Sum.inr ⟨k, q⟩ ∈ ts.consts → k < ts.level :=
  match ts with
  | []ₜ => by simp [Terms.consts]
  | t ∷ₜ ts => by
    intro h
    simp [Terms.consts] at h
    simp [Terms.level]
    cases h with
    | inl h => left; apply Term.const_less_than_level; exact h
    | inr h => right; apply Terms.const_less_than_level; exact h
end
termination_by
  Term.const_less_than_level => t.size
  Terms.const_less_than_level => ts.size

lemma Formula.const_less_than_level {p : Formula 𝓛*} :
  Sum.inr ⟨k, q⟩ ∈ p.consts → k < p.level := by
  intro h
  induction p with
  | atom =>
    simp [Formula.consts] at h
    simp [Formula.level]
    apply Terms.const_less_than_level
    exact h
  | false => simp [Formula.consts] at h
  | implies _ _ ih₁ ih₂ =>
    simp [Formula.consts] at h
    simp [Formula.level]
    cases h with
    | inl h => left; apply ih₁; exact h
    | inr h => right; apply ih₂; exact h
  | all _ ih =>
    simp [Formula.consts] at h
    simp [Formula.level]
    apply ih
    exact h

mutual
lemma Term.level_of_inj_consts {t : Term 𝓛} : ⌈t⌉ₜ.level = 0 :=
  match t with
  | #x => by simp [Term.injConsts, Term.level]
  | Term.func (n := 0) f ([]ₜ) => by simp [Term.injConsts, Term.level]
  | Term.func (n := n + 1) f ts => by
    simp [Term.injConsts, Term.level]
    apply Terms.level_of_inj_consts
lemma Terms.level_of_inj_consts {ts : Terms 𝓛 n} : ⌈ts⌉ₜₛ.level = 0 :=
  match ts with
  | []ₜ => by simp [Terms.injConsts, Terms.level]
  | t ∷ₜ ts => by
    simp [Terms.injConsts, Terms.level]
    rw [Term.level_of_inj_consts, Terms.level_of_inj_consts]
    trivial
end
termination_by
  Term.level_of_inj_consts => t.size
  Terms.level_of_inj_consts => ts.size

lemma Formula.level_of_inj_consts {p : Formula 𝓛} : ⌈p⌉ₚ.level = 0 := by
  induction p <;> simp [Formula.injConsts, Formula.level]
  case atom => simp [Terms.level_of_inj_consts]
  case implies _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  case all _ ih => exact ih

lemma level_of_inj_omega_witness {𝓛 : Language} {c : 𝓛.witnessAcc n} :
  (injOmegaWitness c).fst < n := by
  induction n with
  | zero => cases c
  | succ n ih =>
    cases c with
    | inl c =>
      simp [injOmegaWitness]
      trans
      · exact ih (c := c)
      · simp
    | inr c => simp [injOmegaWitness]

mutual
lemma Term.level_of_inj_omega {t : Term (𝓛^n)} : t.injOmega.level ≤ n :=
  match t with
  | #x => by simp [Term.injOmega, Term.level]
  | Term.func (n := 0) (Sum.inl f) ([]ₜ) => by simp [Term.injOmega, Term.level]
  | Term.func (n := 0) (Sum.inr c) ([]ₜ) => by
    simp [Term.injOmega, Term.level]
    apply level_of_inj_omega_witness
  | Term.func (n := n + 1) f ts => by
    simp [Term.injOmega, Term.level]
    apply Terms.level_of_inj_omega
lemma Terms.level_of_inj_omega {ts : Terms (𝓛^n) m} : ts.injOmega.level ≤ n :=
  match ts with
  | []ₜ => by simp [Terms.injOmega, Terms.level]
  | t ∷ₜ ts => by
    simp [Terms.injOmega, Terms.level]
    constructor
    · apply Term.level_of_inj_omega
    · apply Terms.level_of_inj_omega
end
termination_by
  Term.level_of_inj_omega => t.size
  Terms.level_of_inj_omega => ts.size

theorem Formula.level_of_inj_omega {p : Formula (𝓛^n)} : p.injOmega.level ≤ n := by
  induction p <;> simp [Formula.injOmega, Formula.level]
  case atom => apply Terms.level_of_inj_omega
  case implies _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  case all _ ih => exact ih

mutual
lemma Term.le_level_of_subst :
  n ≤ (t[σ]ₜ).level → n ≤ t.level ∨ ∃ x ∈ t.vars, n ≤ (σ x).level :=
  match t with
  | #x => by simp [Term.subst, Term.level]; exact Or.inr
  | Term.func (n := 0) (Sum.inl f) ([]ₜ) => by simp
  | Term.func (n := 0) (Sum.inr c) ([]ₜ) => by simp
  | Term.func (n := n + 1) f ts => by
    simp [Term.level]
    exact Terms.le_level_of_subst
lemma Terms.le_level_of_subst :
  n ≤ (ts[σ]ₜₛ).level → n ≤ ts.level ∨ ∃ x ∈ ts.vars, n ≤ (σ x).level :=
  match ts with
  | []ₜ => by simp
  | t ∷ₜ ts => by
    simp [Terms.level]
    intro h; cases' h with h h
    · rcases Term.le_level_of_subst h with h' | ⟨x, h', h''⟩
      · exact Or.inl $ Or.inl h'
      · exact Or.inr ⟨x, ⟨Or.inl h', h''⟩⟩
    · rcases Terms.le_level_of_subst h with h' | ⟨x, h', h''⟩
      · exact Or.inl $ Or.inr h'
      · exact Or.inr ⟨x, ⟨Or.inr h', h''⟩⟩
end
termination_by
  Term.le_level_of_subst => t.size
  Terms.le_level_of_subst => ts.size

lemma Formula.le_level_of_subst :
  n ≤ (p[σ]ₚ).level → n ≤ p.level ∨ ∃ x ∈ p.free, n ≤ (σ x).level := by
  intro h
  induction p generalizing σ <;> simp [Formula.level] at *
  case atom => exact Terms.le_level_of_subst h
  case false => exact h
  case implies _ _ ih₁ ih₂ =>
    cases' h with h h
    · rcases ih₁ h with h' | ⟨x, h', h''⟩
      · exact Or.inl $ Or.inl h'
      · exact Or.inr ⟨x, ⟨Or.inl h', h''⟩⟩
    · rcases ih₂ h with h' | ⟨x, h', h''⟩
      · exact Or.inl $ Or.inr h'
      · exact Or.inr ⟨x, ⟨Or.inr h', h''⟩⟩
  case all _ ih =>
    rcases ih h with h | ⟨x, h, h'⟩
    · exact Or.inl h
    · cases' x with x
      · simp [Subst.lift, Term.level] at h'
        simp [h']
      · simp [Subst.lift, Term.shift] at h'
        apply Term.le_level_of_subst at h'
        rcases h' with h' | ⟨y, _, h'⟩
        · right; exists x
        · simp [Subst.shift, Term.level] at h'
          simp [h']

mutual
lemma Term.level_of_subst_le :
  (t[σ]ₜ).level ≤ n → t.level ≤ n ∧ ∀ x ∈ t.vars, (σ x).level ≤ n :=
  match t with
  | #x => by simp [Term.subst, Term.level]
  | Term.func (n := 0) (Sum.inl f) ([]ₜ) => by simp
  | Term.func (n := 0) (Sum.inr c) ([]ₜ) => by simp
  | Term.func (n := n + 1) f ts => by
    simp [Term.level]
    exact Terms.level_of_subst_le
lemma Terms.level_of_subst_le :
  (ts[σ]ₜₛ).level ≤ n → ts.level ≤ n ∧ ∀ x ∈ ts.vars, (σ x).level ≤ n :=
  match ts with
  | []ₜ => by simp
  | t ∷ₜ ts => by
    simp [Terms.level]
    intro h₁ h₂
    rcases Term.level_of_subst_le h₁ with ⟨h₁, h₁'⟩
    rcases Terms.level_of_subst_le h₂ with ⟨h₂, h₂'⟩
    exact ⟨⟨h₁, h₂⟩, λ x h => Or.elim h (h₁' x) (h₂' x)⟩
end
termination_by
  Term.level_of_subst_le => t.size
  Terms.level_of_subst_le => ts.size

lemma Formula.level_of_subst_le :
  (p[σ]ₚ).level ≤ n → p.level ≤ n ∧ ∀ x ∈ p.free, (σ x).level ≤ n := by
  intro h
  induction p generalizing σ <;> simp [Formula.level]
  case atom => exact Terms.level_of_subst_le h
  case implies _ _ ih₁ ih₂ =>
    simp [Formula.level] at h
    rcases h with ⟨h₁, h₂⟩
    rcases ih₁ h₁ with ⟨h₁, h₁'⟩
    rcases ih₂ h₂ with ⟨h₂, h₂'⟩
    exact ⟨⟨h₁, h₂⟩, λ x h => Or.elim h (h₁' x) (h₂' x)⟩
  case all _ ih =>
    simp [Formula.level] at h
    rcases ih h with ⟨h₁, h₂⟩
    constructor
    · exact h₁
    · intros x h
      replace h₂ := h₂ _ h
      simp [Subst.lift, Term.shift] at h₂
      rcases Term.level_of_subst_le h₂ with ⟨h₂, _⟩
      exact h₂

def WitnessFormulas : Formulas 𝓛*
  := { p | ∃ (p' : Formula 𝓛*) (c : Const 𝓛*)
             (n : ℕ) (p'' : Formula (𝓛^n)),
             p = ∃' p' ⟶ p' [↦ₛ c]ₚ
             ∧ p' = p''.injOmega
             ∧ c = Sum.inr ⟨n, p''⟩
             ∧ 0 ∈ p'.free }

notation "𝓦" => WitnessFormulas

lemma level_of_witness_formulas
  {p p' : Formula 𝓛*} {c : Const 𝓛*} {p'' : Formula (𝓛^n)} :
  p = ∃' p' ⟶ p' [↦ₛ c]ₚ →
  p' = p''.injOmega →
  c = Sum.inr ⟨n, p''⟩ →
  0 ∈ p'.free →
  p.level = n + 1 := by
  intros h₁ h₂ h₃ h₄
  subst h₁
  apply Nat.le_antisymm
  · simp [Formula.level]
    have h : Formula.level p' ≤ n
    · rw [h₂]; apply Formula.level_of_inj_omega
    constructor
    · exact Nat.le_succ_of_le h
    · apply Nat.le_of_not_lt
      intro h'
      apply Formula.le_level_of_subst at h'
      rcases h' with h' | ⟨x, h', h''⟩
      · apply Nat.not_le_of_lt h'
        exact Nat.le_succ_of_le h
      · cases' x with x
        · simp [Subst.single, h₃, Term.level] at h''
          exact Nat.not_succ_le_self _ h''
        · simp [Subst.single, Term.level] at h''
  · simp [Formula.level]
    right
    apply Nat.le_of_not_lt
    intro h
    apply Nat.le_of_lt_succ at h
    apply Formula.level_of_subst_le at h
    rcases h with ⟨_, h⟩
    replace h := h _ h₄
    simp [Subst.single, h₃, Term.level] at h

lemma level_less_than_witness_formulas
  {p p' q : Formula 𝓛*} {c : Const 𝓛*} {p'' : Formula (𝓛^n)} :
  p = ∃' p' ⟶ p' [↦ₛ c]ₚ →
  p' = p''.injOmega →
  c = Sum.inr ⟨n, p''⟩ →
  0 ∈ p'.free →
  q ∈ 𝓦 → q.level ≤ p.level →
  q ≠ p →
  c ∉ q.consts := by
  intros h₁' h₂' h₃' h₄' h₁ h₂ h₃ h₄
  rcases h₁ with ⟨q', c', m, q'', h₁'', h₂'', h₃'', h₄''⟩
  simp [h₁'', Formula.consts, Formula.consts_of_subst] at h₄
  rcases h₄ with h₄ | ⟨x, h₄, h₅⟩
  · replace h₄ : n < q'.level
    · subst h₃'; apply Formula.const_less_than_level at h₄; exact h₄
    have h₅ : q'.level ≤ m
    · subst h₂''; apply Formula.level_of_inj_omega
    have h₆ : q.level = m + 1 := 
      level_of_witness_formulas h₁'' h₂'' h₃'' h₄''
    have h₇ : p.level = n + 1 :=
      level_of_witness_formulas h₁' h₂' h₃' h₄'
    have h := trans h₄ h₅
    rw [h₆, h₇] at h₂
    apply Nat.le_of_succ_le_succ at h₂
    exact Nat.not_le_of_lt h h₂
  · cases' x with x
    · simp [Subst.single, Term.consts] at h₅
      subst h₃' h₃''
      injection h₅ with h₅
      injection h₅ with h₅ h₅'
      subst h₅ h₅' h₂' h₂'' h₁' h₁''
      contradiction
    · simp [Subst.single, Term.consts] at h₅

lemma Set.Finite.induction_on_sorted
  {C : Set α → Prop} {S : Set α} (h : S.Finite)
  (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsTotal α r]
  (H0 : C ∅)
  (H1 : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → (∀ x ∈ s, r a x) → C s → C (insert a s)) :
  C S := by
  lift S to Finset α using h
  rcases S with ⟨S, h₁⟩
  unfold Finset.toSet at *; simp at *
  generalize h : List.insertionSort r S.toList = l
  replace h₁ : l.Nodup
  · rw [←h, List.Perm.nodup_iff (List.perm_insertionSort _ _)]
    simp [←Multiset.coe_nodup]
    exact h₁
  have h₂ : l.Sorted r
  · rw [←h]
    apply List.sorted_insertionSort
  have h₃ : ∀ x, x ∈ l ↔ x ∈ S
  · intro x
    rw [←h, ←Multiset.mem_toList]
    apply List.Perm.mem_iff
    apply List.perm_insertionSort
  simp [←h₃]
  replace h₃ : ∀ x, x ∈ l → x ∈ S
  · simp [h₃]
  clear h
  induction' h₂ with a l h₂ _ ih
  · simp; apply H0
  · simp; change C (insert a { x | x ∈ l })
    apply H1
    · apply h₃; simp
    · intros x h; apply h₃; right; exact h
    · intro h
      cases' h₁ with _ _ h₁
      exact h₁ _ h rfl
    · exact h₂
    · apply ih
      · cases' h₁ with _ _ _ h₁
        exact h₁
      · intros x h; apply h₃; right; exact h

lemma consistency_of_witness_formulas_aux {Γ : Formulas 𝓛} :
  Consistent Γ → W ⊆ 𝓦 → Set.Finite W → Consistent (⌈Γ⌉ₚₛ ∪ W) := by
  intros h₁ h₂ h₃
  let r : Formula 𝓛* → Formula 𝓛* → Prop := λ p q => p.level ≥ q.level
  have : DecidableRel r := Classical.decRel r
  have : IsTrans _ r := ⟨λ _ _ _ h₁ h₂ => Nat.le_trans h₂ h₁⟩
  have : IsTotal _ r := ⟨λ _ _ => Nat.le_total _ _⟩
  apply Set.Finite.induction_on_sorted (C := λ W => Consistent (⌈Γ⌉ₚₛ ∪ W)) h₃ r
  · simp; apply consts_keeps_consistency; exact h₁
  · intros p W' h₄ h₅ h₆ h₇ h₈
    simp; apply Consistent.add.mpr
    revert h₈; apply mt; intro h₈
    rcases h₂ h₄ with ⟨p', c, n, p'', h₁', h₂', h₃', h₄'⟩
    rw [h₁'] at h₈
    apply Proof.mp
    · exact Proof.mp Proof.not_imp_left h₈
    · apply const_generalization (c := c)
      · intros q h h'
        cases' h with h h
        · rcases h with ⟨q', h₁'', h₂''⟩
          rw [←h₂'', h₃'] at h'
          apply Formula.const_less_than_level at h'
          rw [Formula.level_of_inj_consts] at h'
          contradiction
        · revert h'
          apply level_less_than_witness_formulas h₁' h₂' h₃' h₄'
          · exact h₂ (h₅ h)
          · exact h₇ _ h
          · intro h'; rw [h'] at h; contradiction
      · intro h
        simp [Formula.consts, h₃'] at h
        apply Formula.const_less_than_level at h
        apply Nat.not_le_of_lt at h
        apply h
        simp [h₂']
        apply Formula.level_of_inj_omega
      · exact Proof.mp Proof.not_imp_right h₈

lemma Set.decompose_subset_union {s₁ s₂ s₃ : Set α} :
  s₁ ⊆ s₂ ∪ s₃ → ∃ s₄ s₅, s₁ = s₄ ∪ s₅ ∧ s₄ ⊆ s₂ ∧ s₅ ⊆ s₃ := by
  intros h
  exists s₁ ∩ s₂
  exists s₁ ∩ s₃
  constructor
  · simp [←Set.inter_distrib_left, Set.inter_eq_self_of_subset_left h]
  constructor <;> simp [h]

theorem consistency_of_witness_formulas :
  Consistent Γ → Consistent (⌈Γ⌉ₚₛ ∪ 𝓦) := by
  intros h₁ h₂
  rcases Proof.compactness h₂ with ⟨Δ, ⟨h₂, ⟨h₃, h₄⟩⟩⟩
  rcases Set.decompose_subset_union h₂ with ⟨Γ', W, h₅, h₆, h₇⟩
  subst h₅
  revert h₄
  apply Consistent.weaken
  · apply Set.union_subset_union_left _ h₆
  apply consistency_of_witness_formulas_aux
  · exact h₁
  · exact h₇
  · apply Set.Finite.subset
    · exact h₃
    · simp


