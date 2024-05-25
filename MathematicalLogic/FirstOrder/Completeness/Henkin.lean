import Mathlib.Data.List.Sort
import MathematicalLogic.FirstOrder.Semantics
import MathematicalLogic.FirstOrder.Completeness.Defs

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
  replace h₁ : l.Nodup := by
    rw [←h, List.Perm.nodup_iff (List.perm_insertionSort _ _)]
    simp [←Multiset.coe_nodup]
    exact h₁
  have h₂ : l.Sorted r := by
    rw [←h]
    apply List.sorted_insertionSort
  have h₃ : ∀ x, x ∈ l ↔ x ∈ S := by
    intro x
    rw [←h, ←Multiset.mem_toList]
    apply List.Perm.mem_iff
    apply List.perm_insertionSort
  simp [←h₃]
  replace h₃ : ∀ x, x ∈ l → x ∈ S := by
    simp [h₃]
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

lemma Set.decompose_subset_union {s₁ s₂ s₃ : Set α} :
  s₁ ⊆ s₂ ∪ s₃ → ∃ s₄ s₅, s₁ = s₄ ∪ s₅ ∧ s₄ ⊆ s₂ ∧ s₅ ⊆ s₃ := by
  intros h
  exists s₁ ∩ s₂
  exists s₁ ∩ s₃
  aesop



namespace FirstOrder.Language

@[reducible]
def addConsts (𝓛 : Language) (𝓒 : Type) [DecidableEq 𝓒] : Language where
  𝓕 := λ
       | 0 => 𝓛.𝓕 0 ⊕ 𝓒
       | n + 1 => 𝓛.𝓕 (n + 1)
  decEq𝓕 :=
    @λ
    | 0, f, g => Sum.instDecidableEqSum f g
    | _ + 1, _, _ => inferInstance
  𝓡 := 𝓛.𝓡
local infix:70 " ⊎ " => Language.addConsts

variable {𝓛 : Language} {𝓒 : Type} [DecidableEq 𝓒]

def Term.injConsts : 𝓛.Term → (𝓛 ⊎ 𝓒).Term
| #x => #x
| Term.func (n := 0) f ([]ᵥ) => Sum.inl f ⬝ₜ []ᵥ
| Term.func (n := _ + 1) f v => f ⬝ₜ λ i => (v i).injConsts

local notation "⌈" t "⌉ₜ" => Term.injConsts t

def Formula.injConsts : 𝓛.Formula → (𝓛 ⊎ 𝓒).Formula
| r ⬝ᵣ v => r ⬝ᵣ λ i => (v i).injConsts
| t₁ ≐ t₂ => t₁.injConsts ≐ t₂.injConsts
| ⊥ => ⊥
| p ⇒ q => p.injConsts ⇒ q.injConsts
| ∀' p => ∀' p.injConsts

local notation "⌈" p "⌉ₚ" => Formula.injConsts p

def Context.injConsts (Γ : 𝓛.Context) : (𝓛 ⊎ 𝓒).Context :=
  { ⌈p⌉ₚ | p ∈ Γ }

local notation "⌈" Γ "⌉ᴳ" => Context.injConsts Γ

def Term.eraseConsts : (𝓛 ⊎ 𝓒).Term → ℕ → 𝓛.Term
| #x, _ => #x
| func (n := 0) (Sum.inl f) []ᵥ, _ => f ⬝ₜ []ᵥ
| func (n := 0) (Sum.inr _) []ᵥ, x => #x
| func (n := _ + 1) f v, x => f ⬝ₜ λ i => (v i).eraseConsts x
local notation "⌊" t "⌋ₜ" => Term.eraseConsts t

def Formula.eraseConsts : (𝓛 ⊎ 𝓒).Formula → ℕ → 𝓛.Formula
| r ⬝ᵣ v, x => r ⬝ᵣ λ i => ⌊v i⌋ₜ x
| t₁ ≐ t₂, x => ⌊t₁⌋ₜ x ≐ ⌊t₂⌋ₜ x
| ⊥, _ => ⊥
| p ⇒ q, x => p.eraseConsts x ⇒ q.eraseConsts x
| ∀' p, x => ∀' (p.eraseConsts (x + 1))
local notation "⌊" p "⌋ₚ" => Formula.eraseConsts p

lemma Term.erase_inj : ⌊(⌈t⌉ₜ : (𝓛 ⊎ 𝓒).Term)⌋ₜ x = t := by
  induction t with
  | var x => simp [injConsts, eraseConsts]
  | @func n f v ih =>
    cases n with simp [injConsts, eraseConsts]
    | zero => simp [Vec.eq_nil]
    | succ => ext; simp [ih]

lemma Formula.erase_inj : ⌊(⌈p⌉ₚ : (𝓛 ⊎ 𝓒).Formula)⌋ₚ x = p := by
  induction p generalizing x with simp [injConsts, eraseConsts]
  | rel r v => simp [Term.erase_inj]
  | eq t₁ t₂ => simp [Term.erase_inj]
  | imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | all _ ih => simp [ih]
  
section

variable {t : (𝓛 ⊎ 𝓒).Term} {σ₁ : (𝓛 ⊎ 𝓒).Subst} {σ₂ : 𝓛.Subst}
  (h₁ : ∀ z, σ₂ z = ⌊σ₁ z⌋ₜ x) (h₂ : σ₂ y = #x)

lemma Term.erase_swap_subst : ⌊t[σ₁]ₜ⌋ₜ x = (⌊t⌋ₜ y)[σ₂]ₜ := by
  induction t with
  | var z => simp [eraseConsts, h₁]
  | @func n f v ih =>
    cases n with
    | zero => cases f <;> simp [eraseConsts, h₂, Vec.eq_nil]
    | succ => simp [eraseConsts]; ext; simp [ih]

lemma Formula.erase_swap_subst : ⌊p[σ₁]ₚ⌋ₚ x = (⌊p⌋ₚ y)[σ₂]ₚ := by
  induction p generalizing σ₁ σ₂ x y with simp [eraseConsts]
  | rel r v | eq t₁ t₂ => simp [Term.erase_swap_subst h₁ h₂]
  | imp p q ih₁ ih₂ => simp [ih₁ h₁ h₂, ih₂ h₁ h₂]
  | all p ih =>
    rw [ih]
    · intro z; cases z
      · rfl
      · simp [Term.shift]
        rw [h₁, Term.erase_swap_subst]
        · simp [Term.eraseConsts]
        · rfl
    · simp [h₂, Term.shift]

end

lemma erase_keeps_axioms {p : (𝓛 ⊎ 𝓒).Formula} :
  p ∈ (𝓛 ⊎ 𝓒).Axioms → ⌊p⌋ₚ x ∈ 𝓛.Axioms := by
  intro h
  induction h generalizing x <;> simp [Formula.eraseConsts] <;> try constructor
  case a4 t p =>
    rw [Formula.erase_swap_subst (σ₂ := ↦ₛ (⌊t⌋ₜ x))]
    · exact .a4
    · intro z; cases z <;> simp [Term.eraseConsts]
    · rfl
  case a5 p =>
    rw [Formula.shift, Formula.erase_swap_subst]
    · exact .a5
    · intro z; simp [Term.eraseConsts]
    · rfl
  case e2 t₁ t₂ p =>
    rw [Formula.erase_swap_subst (y := x + 1), Formula.erase_swap_subst (y := x + 1)]
    · exact .e2
    · intro z; cases z <;> simp [Term.eraseConsts]
    · rfl
    · intro z; cases z <;> simp [Term.eraseConsts]
    · rfl
  case all ih =>
    apply ih

lemma erase_keeps_proof {p : (𝓛 ⊎ 𝓒).Formula} : ⌈Γ⌉ᴳ ⊢ p → Γ ⊢ ⌊p⌋ₚ x := by
  intro h
  induction h with
  | hyp h =>
    rcases h with ⟨p', ⟨h₁, h₂⟩⟩
    subst h₂
    simp [Formula.erase_inj]
    exact Proof.hyp h₁
  | ax h =>
    apply Proof.ax
    apply erase_keeps_axioms
    exact h
  | mp _ _ ih₁ ih₂ =>
    exact ih₁.mp ih₂

theorem consts_keeps_consistency {Γ : 𝓛.Context} :
  Γ.Consistent → (⌈Γ⌉ᴳ : (𝓛 ⊎ 𝓒).Context).Consistent := by
  intros h h₁
  apply erase_keeps_proof (x := 0) at h₁
  apply h
  exact h₁

def Structure.reductConsts (𝓜 : (𝓛 ⊎ 𝓒).Structure) : 𝓛.Structure where
  𝓤 := 𝓜.𝓤
  inhabited𝓤 := inferInstance
  interp𝓕 :=
    @λ
    | 0, f => 𝓜.interp𝓕 (Sum.inl f)
    | _ + 1, f => 𝓜.interp𝓕 f
  interp𝓡 := 𝓜.interp𝓡
local notation "⌊" 𝓜 "⌋ₘ" => Structure.reductConsts 𝓜

lemma Term.interp_reduct : ⟦ t ⟧ₜ ⌊𝓜⌋ₘ, ρ = ⟦ (⌈t⌉ₜ : (𝓛 ⊎ 𝓒).Term) ⟧ₜ 𝓜, ρ := by
  induction t with
  | var x => rfl
  | @func n f v ih =>
    cases n with simp [injConsts, interp]
    | zero => simp [Vec.eq_nil]; rfl
    | succ => simp [ih]; rfl

lemma Formula.interp_reduct :
  ⌊𝓜⌋ₘ ⊨[ρ] p ↔ 𝓜 ⊨[ρ] (⌈p⌉ₚ : (𝓛 ⊎ 𝓒).Formula) := by
  induction p generalizing ρ with simp [injConsts, interp]
  | rel r v => simp [Term.interp_reduct]; rfl
  | eq t₁ t₂ => simp [Term.interp_reduct]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => apply forall_congr'; intro; rw [ih]; rfl

theorem consts_keeps_satisfiability :
  Context.Satisfiable.{u} (⌈Γ⌉ᴳ : (𝓛 ⊎ 𝓒).Context) → Context.Satisfiable.{u} Γ := by
  rintro ⟨𝓜, ⟨ρ, h⟩⟩
  exists ⌊𝓜⌋ₘ
  exists ρ
  intros p h₁
  rw [Formula.interp_reduct]
  apply h
  exists p



def Term.consts : 𝓛.Term → Set 𝓛.Const
| #_ => {}
| Term.func (n := 0) c ([]ᵥ) => {c}
| Term.func (n := _ + 1) _ v => ⋃i, (v i).consts

def Formula.consts : 𝓛.Formula → Set 𝓛.Const
| _ ⬝ᵣ v => ⋃i, (v i).consts
| t₁ ≐ t₂ => t₁.consts ∪ t₂.consts
| ⊥ => {}
| p ⇒ q => p.consts ∪ q.consts
| ∀' p => p.consts

lemma Term.consts_of_subst :
  t[σ]ₜ.consts = t.consts ∪ ⋃ x ∈ t.vars, (σ x).consts := by
  induction t with
  | var x => simp [vars, consts]
  | @func n f v ih =>
    cases n with simp [vars, Term.consts]
    | succ => rw [Set.iUnion_comm, ←Set.iUnion_union_distrib]; simp_rw [ih]

lemma Formula.consts_of_subst :
  p[σ]ₚ.consts = p.consts ∪ ⋃ x ∈ p.free, (σ x).consts := by
  induction p generalizing σ with simp_rw [free, consts]
  | rel r v => simp_rw [Set.biUnion_iUnion, ←Set.iUnion_union_distrib, Term.consts_of_subst]
  | eq t₁ t₂ => simp_rw [Set.biUnion_union, Term.consts_of_subst]; aesop
  | false => simp
  | imp p q ih₁ ih₂ => rw [ih₁, ih₂, Set.biUnion_union]; aesop
  | all p ih =>
    ext c; simp [ih]; apply or_congr_right
    constructor
    · rintro ⟨x, h₁, h₂⟩
      cases x with
      | zero => contradiction
      | succ x =>
        simp [Term.shift, Term.consts_of_subst] at h₂
        rcases h₂ with (h₂ | ⟨_, _, h₃⟩)
        · exists x
        · simp [Term.consts] at h₃
    · rintro ⟨y, ⟨h₁, h₂⟩⟩
      exists y + 1
      constructor
      · exact h₁
      · simp [Term.shift, Term.consts_of_subst]
        left; exact h₂

def Term.substConst : 𝓛.Term → 𝓛.Const → ℕ → 𝓛.Term
| #x, _, y =>
  if x < y then #x else #(x + 1)
| Term.func (n := 0) c ([]ᵥ), c', x =>
  if c = c' then #x else c
| Term.func (n := _ + 1) f v, c, x => f ⬝ₜ λ i => (v i).substConst c x
local notation t "[" c " ↦ᶜ " x "]ₜ" => Term.substConst t c x

def Formula.substConst : 𝓛.Formula → 𝓛.Const → ℕ → 𝓛.Formula
| r ⬝ᵣ v, c, x => r ⬝ᵣ λ i => (v i)[c ↦ᶜ x]ₜ
| t₁ ≐ t₂, c, x => t₁[c ↦ᶜ x]ₜ ≐ t₂[c ↦ᶜ x]ₜ
| ⊥, _, _ => ⊥
| p ⇒ q, c, x => p.substConst c x ⇒ q.substConst c x
| ∀' p, c, x => ∀' (p.substConst c (x + 1))
local notation p "[" c " ↦ᶜ " x "]ₚ" => Formula.substConst p c x

def Subst.shift_since (x : ℕ) : 𝓛.Subst := λ y => if y < x then #y else #(y + 1)

lemma Term.subst_const_of_non_const_aux :
  c ∉ t.consts → t[c ↦ᶜ x]ₜ = t[Subst.shift_since x]ₜ := by
  intro h
  induction t with
  | var y => simp [substConst, Subst.shift_since]
  | @func n f v ih =>
    cases n with (simp [consts] at h; simp [substConst])
    | zero => simp [Ne.symm h, Vec.eq_nil]
    | succ n => ext; apply ih; apply h

lemma Formula.subst_const_of_non_const_aux :
  c ∉ p.consts → p[c ↦ᶜ x]ₚ = p[Subst.shift_since x]ₚ := by
  intro h
  induction p generalizing x with (simp [consts, not_or] at h; simp [substConst])
  | rel r v => ext; apply Term.subst_const_of_non_const_aux; apply h
  | eq t₁ t₂ => constructor <;> apply Term.subst_const_of_non_const_aux <;> aesop
  | imp p q ih₁ ih₂ => rw [ih₁ h.left, ih₂ h.right]
  | all p ih =>
    rw [ih h]
    congr
    funext y
    cases y with simp [Subst.shift_since]
    | succ y =>
      by_cases h : y < x
      · simp [h, Nat.succ_lt_succ h, Term.shift]
      · simp [h, mt Nat.lt_of_succ_lt_succ h, Term.shift]

lemma Formula.subst_const_of_non_const : c ∉ p.consts → p[c ↦ᶜ 0]ₚ = ↑ₚp :=
  subst_const_of_non_const_aux

section

variable {c : 𝓛.Const} {σ₁ σ₂ : 𝓛.Subst}
  (h₁ : ∀ z, σ₂ (if z < y then z else z + 1) = (σ₁ z)[c ↦ᶜ x]ₜ) (h₂ : σ₂ y = #x)

lemma Term.subst_const_swap_subst : t[σ₁]ₜ[c ↦ᶜ x]ₜ = t[c ↦ᶜ y]ₜ[σ₂]ₜ := by
  induction t with
  | var z => simp [substConst, ←h₁]; by_cases h : z < y <;> simp [h]
  | @func n f v ih =>
    cases n with simp [substConst]
    | zero => by_cases h : f = c <;> simp [h, h₂, Vec.eq_nil]
    | succ n => ext; apply ih

lemma Formula.subst_const_swap_subst : p[σ₁]ₚ[c ↦ᶜ x]ₚ = p[c ↦ᶜ y]ₚ[σ₂]ₚ := by
  induction p generalizing σ₁ σ₂ x y with simp [substConst]
  | rel r v => ext; simp [Term.subst_const_swap_subst h₁ h₂]
  | eq t₁ t₂ => simp [Term.subst_const_swap_subst h₁ h₂]
  | imp p q ih₁ ih₂ => rw [ih₁ h₁ h₂, ih₂ h₁ h₂]
  | all p ih =>
    rw [ih]
    · intro z
      cases z with
      | zero => simp [Term.substConst]
      | succ z =>
        replace h₁ := h₁ z
        by_cases h : z < y
        · simp [h] at h₁
          simp [Nat.succ_lt_succ h, h₁, Term.shift]
          rw [Term.subst_const_swap_subst]
          · intro z'; simp [Term.substConst]
            by_cases h : z' < x <;> simp [h]
          · rfl
        · simp [h] at h₁
          simp [mt Nat.lt_of_succ_lt_succ h,  h₁, Term.shift]
          rw [Term.subst_const_swap_subst]
          · intro z'; simp [Term.substConst]
            by_cases h : z' < x <;> simp [h]
          · rfl
    · simp [h₂, Term.shift]

end

theorem subst_const_keeps_axioms :
  p ∈ 𝓛.Axioms → p[c ↦ᶜ x]ₚ ∈ 𝓛.Axioms := by
  intro h
  induction h generalizing x <;> simp [Formula.substConst] <;> try constructor
  case a4 t p =>
    rw [Formula.subst_const_swap_subst (σ₂ := ↦ₛ (t[c ↦ᶜ x]ₜ))]
    · exact .a4
    · intro z
      cases z with simp
      | succ z =>
        by_cases h : z < x
        · simp [h, Nat.succ_lt_succ h, Term.substConst]
        · simp [h, mt Nat.lt_of_succ_lt_succ h, Term.substConst]
    · rfl
  case a5 p =>
    rw [Formula.shift, Formula.subst_const_swap_subst (σ₂ := Subst.shift)]
    · exact .a5
    · intro z
      by_cases h : z < x <;> simp [h, Term.substConst]
    · rfl
  case e2 t₁ t₂ =>
    rw [Formula.subst_const_swap_subst (y := x + 1), Formula.subst_const_swap_subst (y := x + 1)]
    · exact .e2
    · intro z
      cases z with simp
      | succ z =>
        by_cases h : z < x
        · simp [h, Nat.succ_lt_succ h, Term.substConst]
        · simp [h, mt Nat.lt_of_succ_lt_succ h, Term.substConst]
    · simp
    · intro z
      cases z with simp
      | succ z =>
        by_cases h : z < x
        · simp [h, Nat.succ_lt_succ h, Term.substConst]
        · simp [h, mt Nat.lt_of_succ_lt_succ h, Term.substConst]
    · simp
  case all ih =>
    apply ih

theorem subst_const_keeps_proof {p : 𝓛.Formula} :
  (∀ p ∈ Γ, c ∉ p.consts) → Γ ⊢ p → Γ ⊢ ∀' p[c ↦ᶜ 0]ₚ := by
  intros h₁ h
  induction h with
  | hyp h =>
    rw [Formula.subst_const_of_non_const (h₁ _ h)]
    apply Proof.mp (Proof.ax .a5)
    exact Proof.hyp h
  | ax h =>
    apply Proof.ax
    apply Axioms.all
    apply subst_const_keeps_axioms
    exact h
  | mp _ _ ih₁ ih₂ =>
    exact Proof.mp2 (Proof.ax .a6) ih₁ ih₂

theorem const_generalization {c : 𝓛.Const} :
  (∀ p ∈ Γ, c ∉ p.consts) → c ∉ p.consts → Γ ⊢ p[↦ₛ c]ₚ → Γ ⊢ ∀' p := by
  intros h₁ h₂ h₃
  apply subst_const_keeps_proof h₁ at h₃
  rw [Formula.subst_const_swap_subst (σ₂ := (↦ₛ #0))] at h₃
  · rw [Formula.subst_const_of_non_const h₂, Formula.shift_subst_single] at h₃; exact h₃
  · intro z; cases z <;> simp [Term.substConst]
  · rfl



def witAccAux (𝓛 : Language) : (n : ℕ) → Σ (T : Type), DecidableEq T
| 0 => ⟨Empty, inferInstance⟩
| n + 1 =>
  let ⟨𝓛', _⟩ := 𝓛.witAccAux n
  ⟨𝓛' ⊕ (𝓛 ⊎ 𝓛').Formula, inferInstance⟩

def witAcc (𝓛 : Language) (n : ℕ) := (𝓛.witAccAux n).fst
instance : DecidableEq (𝓛.witAcc n) := (𝓛.witAccAux n).snd
@[reducible] def witNth (𝓛 : Language) (n : ℕ) : Type := (𝓛 ⊎ 𝓛.witAcc n).Formula

@[reducible] def addWitNth (𝓛 n) := 𝓛 ⊎ 𝓛.witAcc n
local instance : Pow Language ℕ where
  pow := addWitNth

@[reducible] def witOmega (𝓛 : Language) : Type := Σ n, 𝓛.witNth n
@[reducible] def addWitOmega (𝓛 : Language) := 𝓛 ⊎ 𝓛.witOmega
local postfix:max "*" => Language.addWitOmega

def injWitOmega : {n : ℕ} → 𝓛.witAcc n → 𝓛.witOmega
| _ + 1, Sum.inl c => injWitOmega c
| n + 1, Sum.inr c => ⟨n, c⟩

def Term.injOmega {n : ℕ} : (𝓛^n).Term → (𝓛*).Term
| #x => #x
| Term.func (n := 0) (Sum.inl f) ([]ᵥ) => Sum.inl f ⬝ₜ []ᵥ
| Term.func (n := 0) (Sum.inr c) ([]ᵥ) => Sum.inr (injWitOmega c) ⬝ₜ []ᵥ
| Term.func (n := _ + 1) f v => f ⬝ₜ λ i => (v i).injOmega

def Formula.injOmega {n : ℕ} : (𝓛^n).Formula → (𝓛*).Formula
| r ⬝ᵣ v => r ⬝ᵣ λ i => (v i).injOmega
| t₁ ≐ t₂ => t₁.injOmega ≐ t₂.injOmega
| ⊥ => ⊥
| p ⇒ q => p.injOmega ⇒ q.injOmega
| ∀' p => ∀' (p.injOmega)

def Term.level : (𝓛*).Term → ℕ
| #_ => 0
| Term.func (n := 0) (Sum.inl _) ([]ᵥ) => 0
| Term.func (n := 0) (Sum.inr c) ([]ᵥ) => c.fst + 1
| Term.func (n := _ + 1) _ v => Vec.max λ i => (v i).level

def Formula.level : (𝓛*).Formula → ℕ
| _ ⬝ᵣ v => Vec.max λ i => (v i).level
| t₁ ≐ t₂ => max t₁.level t₂.level
| ⊥ => 0
| p ⇒ q => max p.level q.level
| ∀' p => p.level

lemma Term.const_less_than_level {t : (𝓛*).Term} :
  Sum.inr ⟨k, q⟩ ∈ t.consts → k < t.level := by
  intro h
  induction t with
  | var x => simp [consts] at h
  | @func n f v ih =>
    cases n with simp [consts] at h
    | zero => subst h; simp [level]
    | succ n =>
      simp [level]
      rcases h with ⟨i, h⟩
      apply le_trans' Vec.le_max
      apply ih; exact h

lemma Formula.const_less_than_level {p : (𝓛*).Formula} :
  Sum.inr ⟨k, q⟩ ∈ p.consts → k < p.level := by
  intro h
  induction p with (simp [consts] at h <;> simp [level])
  | rel r v =>
    rcases h with ⟨i, h⟩
    apply le_trans' Vec.le_max
    apply Term.const_less_than_level
    exact h
  | eq t₁ t₂ =>
    cases h with
    | inl h => left; apply Term.const_less_than_level; exact h
    | inr h => right; apply Term.const_less_than_level; exact h
  | imp p q ih₁ ih₂ =>
    cases h with
    | inl h => left; apply ih₁; exact h
    | inr h => right; apply ih₂; exact h
  | all p ih => apply ih; exact h

lemma Term.level_of_inj_consts {t : 𝓛.Term} : ⌈t⌉ₜ.level = 0 := by
  induction t with
  | var => simp [injConsts, level]
  | @func n f v ih =>
    cases n with simp [injConsts, level]
    | succ n => simp [ih]

lemma Formula.level_of_inj_consts {p : 𝓛.Formula} : ⌈p⌉ₚ.level = 0 := by
  induction p with simp [injConsts, level]
  | rel r v | eq t₁ t₂ => simp [Term.level_of_inj_consts]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => exact ih

lemma level_of_inj_wit_omega {c : 𝓛.witAcc n} : (injWitOmega c).fst < n := by
  induction n with
  | zero => cases c
  | succ n ih =>
    cases c with simp [injWitOmega]
    | inl c => exact Nat.lt_of_lt_of_le ih (Nat.le_succ _)

lemma Term.level_of_inj_omega {n : ℕ} {t : (𝓛^n).Term} : t.injOmega.level ≤ n := by
  induction t with
  | var => simp [injOmega, level]
  | @func n f v ih =>
    cases n with
    | zero => cases f <;> simp [injOmega, level]; exact level_of_inj_wit_omega
    | succ n => simp [injOmega, level]; apply Vec.max_le; exact ih

theorem Formula.level_of_inj_omega {n : ℕ} {p : (𝓛^n).Formula} : p.injOmega.level ≤ n := by
  induction p with simp [injOmega, level]
  | rel r v => apply Vec.max_le; intro; exact Term.level_of_inj_omega
  | eq t₁ t₂ => constructor <;> exact Term.level_of_inj_omega
  | imp p q ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | all p ih => exact ih

lemma Term.le_level_of_subst :
  n ≤ (t[σ]ₜ).level → n ≤ t.level ∨ ∃ x ∈ t.vars, n ≤ (σ x).level := by
  intro h
  induction t with
  | var x => simp [vars, level]; right; exact h
  | @func n f v ih =>
    cases n with
    | zero => cases f <;> simp [subst, vars, level] at * <;> exact h
    | succ n =>
      simp [subst, vars, level, Vec.le_max_iff] at *
      rcases h with ⟨i, h⟩
      apply ih at h
      aesop

lemma Formula.le_level_of_subst :
  n ≤ (p[σ]ₚ).level → n ≤ p.level ∨ ∃ x ∈ p.free, n ≤ (σ x).level := by
  intro h
  induction p generalizing σ with simp [Formula.free, Formula.level] at *
  | @rel n r v =>
    cases n with
    | zero => simp [Vec.max] at *; exact h
    | succ n =>
      simp [Vec.le_max_iff] at *
      rcases h with ⟨i, h⟩
      apply Term.le_level_of_subst at h
      aesop
  | eq t₁ t₂ => rcases h with (h | h) <;> apply Term.le_level_of_subst at h <;> aesop
  | false => exact h
  | imp p q ih₁ ih₂ =>
    rcases h with (h | h)
    · apply ih₁ at h; aesop
    · apply ih₂ at h; aesop
  | all p ih =>
    rcases ih h with h | ⟨x, h, h'⟩
    · left; exact h
    · cases x with
      | zero => simp [Term.level] at h'; simp [h']
      | succ x =>
        simp [Term.shift] at h'
        apply Term.le_level_of_subst at h'
        rcases h' with h' | ⟨y, _, h'⟩
        · right; exists x
        · simp [Term.level] at h'; simp [h']

lemma Term.level_of_subst_le :
  (t[σ]ₜ).level ≤ n → t.level ≤ n ∧ ∀ x ∈ t.vars, (σ x).level ≤ n := by
  intro h
  induction t with
  | var x => simp [subst, vars, level] at *; exact h
  | @func n f v ih =>
    cases n with
    | zero => cases f <;> simp [vars, Vec.eq_nil] at * <;> exact h
    | succ n =>
      simp [vars, level, Vec.max_le_iff] at *
      constructor
      · intro i; exact (ih _ (h _)).left
      · intros x i h'; exact (ih _ (h _)).right _ h'

lemma Formula.level_of_subst_le :
  (p[σ]ₚ).level ≤ n → p.level ≤ n ∧ ∀ x ∈ p.free, (σ x).level ≤ n := by
  intro h
  induction p generalizing σ with simp [free, level] at *
  | rel r v =>
    simp [Vec.max_le_iff] at *
    constructor
    · intro i; exact (Term.level_of_subst_le (h _)).left
    · intros x i h'; exact (Term.level_of_subst_le (h _)).right _ h'
  | eq t₁ t₂ =>
    rcases h with ⟨h₁, h₂⟩
    apply Term.level_of_subst_le at h₁
    apply Term.level_of_subst_le at h₂
    aesop
  | imp p q ih₁ ih₂ =>
    rcases h with ⟨h₁, h₂⟩
    apply ih₁ at h₁
    apply ih₂ at h₂
    aesop
  | all p ih =>
    rcases ih h with ⟨h₁, h₂⟩
    constructor
    · exact h₁
    · intros x h
      replace h₂ := h₂ _ h
      simp [Term.shift] at h₂
      exact (Term.level_of_subst_le h₂).left

lemma exists_inj_wit_omega {c : 𝓛.witOmega} :
  c.fst + 1 ≤ n → ∃ (c' : 𝓛.witAcc n), c = injWitOmega c' := by
  cases' c with k c
  simp
  intro h
  induction' h with n _ ih
  · exists Sum.inr c
  · rcases ih with ⟨c', h⟩
    exists Sum.inl c'

lemma Term.exists_inj_omega :
  t.level ≤ n → ∃ (t' : Term (𝓛^n)), t = t'.injOmega := by
  intro h
  induction t with
  | var x => exists #x
  | @func n f v ih =>
    cases n with
    | zero =>
      simp [Vec.eq_nil] at *
      cases f with
      | inl f => exists Sum.inl f ⬝ₜ []ᵥ
      | inr c =>
        simp [level] at h
        rcases exists_inj_wit_omega h with ⟨c', h⟩
        exists Sum.inr c' ⬝ₜ []ᵥ
        simp [h, injOmega]
    | succ n =>
      simp [level, Vec.max_le_iff] at h
      choose v h using λ i => ih _ (h i)
      exists f ⬝ₜ v
      simp [injOmega]; ext; simp [h]

lemma Formula.exists_inj_omega :
  p.level ≤ n → ∃ (p' : Formula (𝓛^n)), p = p'.injOmega := by
  intro h
  induction p with simp [level] at h
  | rel r v =>
    simp [Vec.max_le_iff] at h
    choose v h using λ i => Term.exists_inj_omega (h i)
    exists r ⬝ᵣ v
    simp [injOmega]; ext; simp [h]
  | eq t₁ t₂ =>
    rcases h with ⟨h₁, h₂⟩
    rcases Term.exists_inj_omega h₁ with ⟨t₁', h₁⟩
    rcases Term.exists_inj_omega h₂ with ⟨t₂', h₂⟩
    exists t₁' ≐ t₂'
    simp [injOmega, h₁, h₂]
  | false => exists ⊥
  | imp p q ih₁ ih₂ =>
    rcases h with ⟨h₁, h₂⟩
    rcases ih₁ h₁ with ⟨p', h₁⟩
    rcases ih₂ h₂ with ⟨q', h₂⟩
    exists p' ⇒ q'
    simp [injOmega, h₁, h₂]
  | all p ih =>
    rcases ih h with ⟨p', h⟩
    exists ∀' p'
    simp [injOmega, h]



def HenkinFormulas (𝓛 : Language) : (𝓛*).Context
  := { p | ∃ (p' : (𝓛*).Formula) (c : (𝓛*).Const) (n : ℕ) (p'' : (𝓛^n).Formula),
             p = ∃' p' ⇒ p' [↦ₛ c]ₚ ∧ p' = p''.injOmega ∧ c = Sum.inr ⟨n, p''⟩ ∧ 0 ∈ p'.free }

section

variable {p p' : (𝓛*).Formula} {p'' : (𝓛^n).Formula} {c : (𝓛*).Const}
  (h₁ : p = ∃' p' ⇒ p' [↦ₛ c]ₚ) (h₂ : p' = p''.injOmega)
  (h₃ : c = Sum.inr ⟨n, p''⟩) (h₄ : 0 ∈ p'.free)

lemma level_of_henkin_formula : p.level = n + 1 := by
  subst h₁
  apply Nat.le_antisymm
  · simp [Formula.level]
    have h : Formula.level p' ≤ n := by
      rw [h₂]; apply Formula.level_of_inj_omega
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

lemma level_less_than_henkin_formula :
  q ∈ 𝓛.HenkinFormulas → q.level ≤ p.level → q ≠ p → c ∉ q.consts := by
  intros h₁' h₂' h₃' h₄'
  rcases h₁' with ⟨q', c', m, q'', h₁'', h₂'', h₃'', h₄''⟩
  simp [h₁'', Formula.consts, Formula.consts_of_subst] at h₄'
  rcases h₄' with h₄' | ⟨x, h₄', h₅'⟩
  · replace h₄' : n < q'.level := by
      subst h₃; apply Formula.const_less_than_level; exact h₄'
    have h₅' : q'.level ≤ m := by
      subst h₂''; apply Formula.level_of_inj_omega
    have h₆' : q.level = m + 1 :=
      level_of_henkin_formula h₁'' h₂'' h₃'' h₄''
    have h₇' : p.level = n + 1 :=
      level_of_henkin_formula h₁ h₂ h₃ h₄
    rw [h₆', h₇'] at h₂'
    apply Nat.le_of_succ_le_succ at h₂'
    exact Nat.not_le_of_lt (Nat.le_trans h₄' h₅') h₂'
  · cases' x with x
    · simp [Subst.single, Term.consts] at h₅'
      subst h₃ h₃''
      injection h₅' with h₅'
      injection h₅' with h₅' h₅''
      subst h₁ h₁'' h₂ h₂'' h₅' h₅''
      contradiction
    · simp [Term.consts] at h₅'

end

lemma consistency_of_henkin_formulas_aux {Γ : 𝓛.Context} :
  Γ.Consistent → W ⊆ 𝓛.HenkinFormulas → Set.Finite W → (⌈Γ⌉ᴳ ∪ W).Consistent := by
  intros h₁ h₂ h₃
  let r : Formula 𝓛* → Formula 𝓛* → Prop := λ p q => p.level ≥ q.level
  have : DecidableRel r := Classical.decRel r
  have : IsTrans _ r := ⟨λ _ _ _ h₁ h₂ => Nat.le_trans h₂ h₁⟩
  have : IsTotal _ r := ⟨λ _ _ => Nat.le_total _ _⟩
  apply Set.Finite.induction_on_sorted (C := λ W => (⌈Γ⌉ᴳ ∪ W).Consistent) h₃ r
  · simp; apply consts_keeps_consistency; exact h₁
  · intros p W' h₄ h₅ h₆ h₇ h₈
    simp; apply Context.Consistent.append.mpr
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
          apply level_less_than_henkin_formula h₁' h₂' h₃' h₄'
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

theorem consistency_of_henkin_formulas {Γ : 𝓛.Context} :
  Γ.Consistent → (⌈Γ⌉ᴳ ∪ 𝓛.HenkinFormulas).Consistent := by
  intros h₁ h₂
  rcases Proof.compactness h₂ with ⟨Δ, ⟨h₂, ⟨h₃, h₄⟩⟩⟩
  rcases Set.decompose_subset_union h₂ with ⟨Γ', W, h₅, h₆, h₇⟩
  subst h₅
  revert h₄
  apply Context.Consistent.weaken
  · apply Set.union_subset_union_left _ h₆
  apply consistency_of_henkin_formulas_aux
  · exact h₁
  · exact h₇
  · apply Set.Finite.subset
    · exact h₃
    · simp

theorem henkin_formulas_saturated {Γ : (𝓛*).Context} :
  𝓛.HenkinFormulas ⊆ Γ → Γ.Saturated := by
  intros h₁ p h₂
  by_cases h₃ : 0 ∈ p.free
  · rcases Formula.exists_inj_omega (p := p) (le_refl _) with ⟨p', h⟩
    let c : (𝓛*).Const := Sum.inr ⟨p.level, p'⟩
    exists c
    apply Proof.mp
    · apply Proof.hyp
      apply h₁
      exists p, c, p.level, p'
    · exact h₂
  · exists Sum.inr ⟨0, (⊥ : Formula _)⟩
    rw [←Formula.is_shift_iff] at h₃
    rcases h₃ with ⟨p', h₃⟩
    rw [h₃, Formula.shift_subst_single]
    apply Proof.mp Proof.exists_self
    rw [←h₃]
    exact h₂
