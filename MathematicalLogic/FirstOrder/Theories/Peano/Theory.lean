import MathematicalLogic.FirstOrder.Theories.Order.Theory

namespace FirstOrder.Language

private inductive peano.Func : ℕ → Type where
| zero : Func 0
| succ : Func 1
| add : Func 2
| mul : Func 2

/-- The language of first-order arithmetic. -/
def peano : Language where
  Func := peano.Func
  Rel _ := Empty

variable {t₁ t₂ : peano.Term n}

namespace peano

def succ (t : peano.Term n) : peano.Term n := .succ ⬝ᶠ [t]ᵥ
scoped notation "S" => succ

instance : Zero (peano.Term n) := ⟨(.zero ⬝ᶠ []ᵥ)⟩
instance : Add (peano.Term n) := ⟨(.add ⬝ᶠ [·, ·]ᵥ)⟩
instance : Mul (peano.Term n) := ⟨(.mul ⬝ᶠ [·, ·]ᵥ)⟩

def ofNat : ℕ → peano.Term n
| 0 => 0
| n + 1 => S (ofNat n)
instance : Coe ℕ (peano.Term m) := ⟨ofNat⟩

def ofEncode [Encodable α] (a : α) : peano.Term n := ofNat (Encodable.encode a)
scoped notation "⌜" a "⌝" => ofEncode a

@[simp] theorem zero_eq : (.zero ⬝ᶠ []ᵥ : peano.Term n) = 0 := rfl
@[simp] theorem succ_eq : (.succ ⬝ᶠ [t₁]ᵥ : peano.Term n) = S t₁ := rfl
@[simp] theorem add_eq : (.add ⬝ᶠ [t₁, t₂]ᵥ : peano.Term n) = t₁ + t₂ := rfl
@[simp] theorem mul_eq : (.mul ⬝ᶠ [t₁, t₂]ᵥ : peano.Term n) = t₁ * t₂ := rfl
@[simp] theorem ofNat_zero : (ofNat 0 : peano.Term n) = 0 := rfl
@[simp] theorem ofNat_succ : ofNat (a + 1) = S (ofNat a : peano.Term n) := rfl

@[simp] theorem subst_zero {σ : peano.Subst n m} : 0[σ]ₜ = 0 := by simp [←zero_eq, Vec.eq_nil]
@[simp] theorem subst_succ : (S t)[σ]ₜ = S (t[σ]ₜ) := by simp [←succ_eq, Vec.eq_one]
@[simp] theorem subst_add : (t₁ + t₂)[σ]ₜ = t₁[σ]ₜ + t₂[σ]ₜ := by simp [←add_eq, Vec.eq_two]
@[simp] theorem subst_mul : (t₁ * t₂)[σ]ₜ = t₁[σ]ₜ * t₂[σ]ₜ := by simp [←mul_eq, Vec.eq_two]
@[simp] theorem subst_ofNat : (ofNat n)[σ]ₜ = ofNat n := by
  induction n with simp
  | succ n ih => simp [ih]
@[simp] theorem subst_ofEncode [Encodable α] {a : α} : (⌜a⌝)[σ]ₜ = ⌜a⌝ := subst_ofNat

@[simp] theorem shift_zero : ↑ₜ(0 : peano.Term n) = 0 := subst_zero
@[simp] theorem shift_succ : ↑ₜ(S t) = S ↑ₜt := subst_succ
@[simp] theorem shift_add : ↑ₜ(t₁ + t₂) = ↑ₜt₁ + ↑ₜt₂ := subst_add
@[simp] theorem shift_mul : ↑ₜ(t₁ * t₂) = ↑ₜt₁ * ↑ₜt₂ := subst_mul
@[simp] theorem shift_ofNat : ↑ₜ(ofNat n : peano.Term m) = ofNat n := subst_ofNat
@[simp] theorem shift_ofEncode [Encodable α] {a : α} : ↑ₜ(⌜a⌝ : peano.Term n) = ⌜a⌝ := shift_ofNat

@[simp] theorem shiftN_ofNat : ↑ₜ^[k] (ofNat n : peano.Term m) = ofNat n := by
  induction k with simp [Term.shiftN]
  | succ k ih => simp [ih]

instance : Order peano where
  leDef := ∃' (#0 + #1 ≐ #2)
  ltDef := ∃' (#0 + S #1 ≐ #2)

theorem le_def : t₁ ⪯ t₂ = ∃' (#0 + ↑ₜt₁ ≐ ↑ₜt₂) := by simp [Order.le, Order.leDef]

theorem lt_def : t₁ ≺ t₂ = S t₁ ⪯ t₂ := by simp [Order.lt, Order.ltDef, le_def]

open Proof

@[prw] theorem eq_congr_succ : Γ ⊢ t₁ ≐ t₂ ⇒ S t₁ ≐ S t₂ := by
  pintro; papply eq_congr_func; papply andN_intro; intro i; cases i using Fin.cases1; passumption

@[prw] theorem eq_congr_add : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ + t₂ ≐ t₁' + t₂' := by
  pintros; papply eq_congr_func; papply andN_intro; intro i; cases i using Fin.cases2 <;> passumption

@[prw] theorem eq_congr_mul : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ * t₂ ≐ t₁' * t₂' := by
  pintros; papply eq_congr_func; papply andN_intro; intro i; cases i using Fin.cases2 <;> passumption

open Std Lean.Parser in
instance : Repr peano where
  reprFunc
  | .zero, _, _ => "0"
  | .succ, prec, v => Repr.addAppParen ("S " ++ v 0 argPrec) prec
  | .add, prec, v => (if prec ≥ 65 then Format.paren else id) (v 0 65 ++ " + " ++ v 1 65)
  | .mul, prec, v => (if prec ≥ 70 then Format.paren else id) (v 0 70 ++ " * " ++ v 1 70)
  reprRel r := nomatch r

end peano

namespace Theory

open peano Proof

attribute [local simp] Term.shift_subst_single Term.shift_subst_assign Term.shift_subst_lift Formula.shift_subst_single

/-- Robinson's Q. -/
inductive Q : peano.Theory where
| ax_succ_ne_zero : Q (∀' (~ S #0 ≐ 0))
| ax_succ_inj : Q (∀' ∀' ((S #1 ≐ S #0) ⇒ #1 ≐ #0))
| ax_add_zero : Q (∀' (#0 + 0 ≐ #0))
| ax_add_succ : Q (∀' ∀' (#1 + S #0 ≐ S (#1 + #0)))
| ax_mul_zero : Q (∀' (#0 * 0 ≐ 0))
| ax_mul_succ : Q (∀' ∀' (#1 * S #0 ≐ #1 * #0 + #1))
| ax_zero_or_succ : Q (∀' (#0 ≐ 0 ⩒ ∃' (#1 ≐ S #0)))

namespace Q

theorem succ_ne_zero (t) : ↑ᵀ^[n] Q ⊢ ~ S t ≐ 0 := by
  have := foralls_elim [t]ᵥ (hyp ax_succ_ne_zero)
  simp at this; exact this

theorem succ_inj : ↑ᵀ^[n] Q ⊢ S t₁ ≐ S t₂ ⇒ t₁ ≐ t₂ := by
  have := foralls_elim [t₂, t₁]ᵥ (hyp ax_succ_inj)
  simp at this; exact this

theorem add_zero (t) : ↑ᵀ^[n] Q ⊢ t + 0 ≐ t := by
  have := foralls_elim [t]ᵥ (hyp ax_add_zero)
  simp at this; exact this

theorem add_succ (t₁ t₂) : ↑ᵀ^[n] Q ⊢ t₁ + S t₂ ≐ S (t₁ + t₂) := by
  have := foralls_elim [t₂, t₁]ᵥ (hyp ax_add_succ)
  simp at this; exact this

theorem mul_zero (t) : ↑ᵀ^[n] Q ⊢ t * 0 ≐ 0 := by
  have := foralls_elim [t]ᵥ (hyp ax_mul_zero)
  simp at this; exact this

theorem mul_succ (t₁ t₂) : ↑ᵀ^[n] Q ⊢ t₁ * S t₂ ≐ t₁ * t₂ + t₁ := by
  have := foralls_elim [t₂, t₁]ᵥ (hyp ax_mul_succ)
  simp at this; exact this

theorem zero_or_succ (t) : ↑ᵀ^[n] Q ⊢ t ≐ 0 ⩒ ∃' (↑ₜt ≐ S #0) := by
  have := foralls_elim [t]ᵥ (hyp ax_zero_or_succ)
  simp at this; exact this

theorem succ_inj_iff : ↑ᵀ^[n] Q ⊢ S t₁ ≐ S t₂ ⇔ t₁ ≐ t₂ := by
  papply iff_intro
  · pexact succ_inj
  · pintro; prw [0]; prefl

theorem eq_succ_of_ne_zero : ↑ᵀ^[n] Q ⊢ ~ t ≐ 0 ⇒ ∃' (↑ₜt ≐ S #0) := zero_or_succ _

lemma add_eq_zero_left : ↑ᵀ^[n] Q ⊢ t₁ + t₂ ≐ 0 ⇒ t₁ ≐ 0 := by
  pintro
  papply or_elim
  · pexact zero_or_succ t₂
  · pintro; prw [←add_zero t₁, ←0, 1, 0]; prefl
  · papply exists_elim'
    pintros; simp
    papply false_elim
    papply succ_ne_zero (↑ₜt₁ + #0)
    prw [←add_succ, ←0]
    passumption

theorem le_of_add_eq : ↑ᵀ^[n] Q ⊢ t₁ + t₂ ≐ t₃ ⇒ t₂ ⪯ t₃ := by
  pintro
  papply exists_intro t₁
  simp
  passumption

theorem zero_le : ↑ᵀ^[n] Q ⊢ 0 ⪯ t := by
  papply exists_intro t; simp
  prw [add_zero]
  prefl

theorem succ_not_le_zero : ↑ᵀ^[n] Q ⊢ ~ S t ⪯ 0 := by
  pintro
  papply exists_elim
  · passumption 0
  · pintro; simp; prw [add_succ]; pexact succ_ne_zero

theorem succ_le_succ_iff : ↑ᵀ^[n] Q ⊢ S t₁ ⪯ S t₂ ⇔ t₁ ⪯ t₂ := by
  papply iff_intro
  · papply exists_elim'
    pintros 2; simp
    papply exists_intro #0; simp
    papply succ_inj
    prw [←0, add_succ]
    prefl
  · papply exists_elim'
    pintros 2; simp
    papply exists_intro #0; simp
    prw [←0, add_succ]
    prefl

theorem not_lt_zero : ↑ᵀ^[n] Q ⊢ ~ t ≺ 0 := by
  simp [lt_def]
  pexact succ_not_le_zero

theorem lt_succ_iff : ↑ᵀ^[n] Q ⊢ t₁ ≺ S t₂ ⇔ t₁ ⪯ t₂ := by
  simp [lt_def]
  pexact succ_le_succ_iff

theorem succ_lt_succ_iff : ↑ᵀ^[n] Q ⊢ S t₁ ≺ S t₂ ⇔ t₁ ≺ t₂ := by
  simp [lt_def]
  pexact succ_le_succ_iff

variable {a b : ℕ}

theorem add_ofNat :
  ↑ᵀ^[n] Q ⊢ a + b ≐ (a + b : ℕ) := by
  induction b with simp
  | zero => apply add_zero
  | succ b ih => prw [add_succ, ih]; prefl

theorem mul_ofNat :
  ↑ᵀ^[n] Q ⊢ a * b ≐ (a * b : ℕ) := by
  induction b with simp
  | zero => apply mul_zero
  | succ b ih => prw [mul_succ, ih, add_ofNat]; prefl

theorem ne_ofNat (h : a ≠ b) : ↑ᵀ^[n] Q ⊢ ~ a ≐ b := by
  induction b generalizing a with
  | zero =>
    cases a <;> simp at h; pexact succ_ne_zero
  | succ b ih =>
    cases a with simp
    | zero => prw [Proof.ne_comm]; pexact succ_ne_zero
    | succ a => simp at h; prw [succ_inj_iff]; exact ih h

theorem le_ofNat (h : a ≤ b) : ↑ᵀ^[n] Q ⊢ a ⪯ b := by
  papply exists_intro (b - a)
  simp
  prw [add_ofNat]
  rw [Nat.sub_add_cancel h]
  prefl

theorem lt_ofNat (h : a < b) :↑ᵀ^[n] Q ⊢ a ≺ b := by
  simp [lt_def]
  exact le_ofNat h

theorem not_le_ofNat (h : b < a) : ↑ᵀ^[n] Q ⊢ ~ a ⪯ b := by
  induction b generalizing a with simp
  | zero =>
    cases a <;> simp at h
    simp; pexact succ_not_le_zero
  | succ b ih =>
    cases a <;> simp at h
    simp; prw [succ_le_succ_iff]
    exact ih h

theorem not_lt_ofNat (h : b ≤ a) : ↑ᵀ^[n] Q ⊢ ~ a ≺ b := by
  simp [lt_def]
  exact not_le_ofNat (Nat.lt_succ_of_le h)

theorem eq_or_ge_ofNat (t) (a : ℕ) : ↑ᵀ^[n] Q ⊢ (⋁ (i : Fin a), t ≐ i) ⩒ a ⪯ t := by
  induction a generalizing n t with simp
  | zero => papply or_inr; pexact zero_le
  | succ a ih =>
    papply or_elim
    · pexact zero_or_succ t
    · pintro
      papply or_inl
      papply orN_intro 0
      passumption
    · papply exists_elim'
      pintros 2
      papply or_elim
      · pexact ih (t := #0)
      · papply orN_elim'
        intro i
        pintro
        papply or_inl; simp [Formula.subst_orN]
        papply orN_intro i.succ; rw [←Term.shift]; simp
        prw [1, succ_inj_iff]
        passumption
      · pintro
        papply or_inr; simp; rw [←Term.shift]
        prw [1, succ_le_succ_iff]
        passumption

theorem lt_or_ge_ofNat (t) (a : ℕ) : ↑ᵀ^[n] Q ⊢ t ≺ a ⩒ a ⪯ t := by
  papply or_elim
  · exact eq_or_ge_ofNat t a
  · papply orN_elim'
    intro ⟨i, h⟩
    pintro
    papply or_inl
    prw [0]
    pexact lt_ofNat h
  · pexact or_inr

theorem eq_or_gt_ofNat (t) (a : ℕ) : ↑ᵀ^[n] Q ⊢ (⋁ (i : Fin (a + 1)), t ≐ i) ⩒ a ≺ t := by
  simp [lt_def]; rw [←ofNat_succ]
  exact eq_or_ge_ofNat t (a + 1)

theorem le_or_gt_ofNat (t) (a : ℕ) : ↑ᵀ^[n] Q ⊢ t ⪯ a ⩒ a ≺ t := by
  prw [←lt_succ_iff]; rw [←ofNat_succ]; nth_rw 2 [lt_def]
  exact lt_or_ge_ofNat t (a + 1)

theorem lt_ofNat_iff : ↑ᵀ^[n] Q ⊢ t ≺ a ⇔ ⋁ (i : Fin a), t ≐ i := by
  papply iff_intro
  · induction a generalizing n with
    | zero =>
      pintro
      papply not_lt_zero at 0
      papply false_elim
      passumption
    | succ m ih =>
      pintro
      papply or_elim
      · pexact zero_or_succ t
      · pintro
        papply orN_intro 0
        passumption
      · papply exists_elim'
        pintros 2; simp
        phave #0 ≺ m
        · prw [←succ_lt_succ_iff, ←0]
          passumption
        · papply ih at 0
          prevert
          papply orN_elim'
          intro i
          pintro
          simp [Formula.shift, Formula.subst_orN]
          papply orN_intro i.succ
          rw [←Term.shift]; prw [1, 0]
          prefl
  · papply orN_elim'
    intro ⟨i, h⟩
    pintro
    prw [0]
    pexact lt_ofNat h

theorem le_ofNat_iff : ↑ᵀ^[n] Q ⊢ t ⪯ a ⇔ ⋁ (i : Fin (a + 1)), t ≐ i := by
  prw [←lt_succ_iff]
  rw [←ofNat_succ]
  prw [lt_ofNat_iff]
  prefl

theorem not_lt_ofNat_iff : ↑ᵀ^[n] Q ⊢ ~ t ≺ a ⇔ a ⪯ t := by
  papply iff_intro
  · pexact lt_or_ge_ofNat t a
  · pintro
    prw [lt_ofNat_iff, neg_orN_iff]
    papply andN_intro
    intro ⟨i, h⟩
    pintro
    prw [0] at 1
    papply not_le_ofNat h at 1
    passumption

theorem not_le_ofNat_iff : ↑ᵀ^[n] Q ⊢ ~ t ⪯ a ⇔ a ≺ t := by
  simp [lt_def]
  prw [←lt_succ_iff]
  rw [←ofNat_succ]
  prw [not_lt_ofNat_iff, lt_succ_iff]
  prefl

theorem ne_ofNat_iff : ↑ᵀ^[n] Q ⊢ ~ t ≐ a ⇔ t ≺ a ⩒ a ≺ t := by
  papply iff_intro
  · pintro
    papply or_elim
    · pexact le_or_gt_ofNat t a
    · prw [le_ofNat_iff]
      papply orN_elim'
      intro ⟨i, h⟩
      pintro
      simp [Nat.lt_succ_iff_lt_or_eq] at h; rcases h with h | h
      · papply or_inl
        prw [0]
        pexact lt_ofNat h
      · simp [h]
        papplya 1 at 0
        papply false_elim
        passumption
    · pexact or_inr
  · papply or_elim' <;> pintros <;> prw [0] at 1 <;> papply not_lt_ofNat (le_refl a) at 1 <;> passumption

theorem bdall_ofNat_iff : ↑ᵀ^[n] Q ⊢ ∀[≺ a] p ⇔ ⋀ (i : Fin a), p[↦ₛ i]ₚ := by
  papply iff_intro
  · pintro
    apply andN_intro
    intro ⟨i, h⟩
    papply forall_elim i at 0; simp
    papplya 0
    pexact lt_ofNat h
  · pintros; simp [Formula.shift, Formula.subst_andN]
    prw [lt_ofNat_iff] at 0
    papply orN_elim
    · passumption
    · intro i
      pintro
      papply andN_elim i at 2
      simp [←Formula.subst_comp]
      prw [←0] at 2
      rw [Subst.zero_cons_shift, Formula.subst_id]
      passumption

theorem bdex_ofNat_iff : ↑ᵀ^[n] Q ⊢ ∃[≺ a] p ⇔ ⋁ (i : Fin a), p[↦ₛ i]ₚ := by
  papply iff_intro
  · papply exists_elim'
    pintro; simp [Formula.shift, Formula.subst_orN, ←Formula.subst_comp]
    prw [and_imp_iff]
    pintros
    prw [lt_ofNat_iff] at 1
    papply orN_elim
    · passumption
    · intro i
      pintro
      papply orN_intro i
      prw [←0]
      rw [Subst.zero_cons_shift, Formula.subst_id]
      passumption
  · papply orN_elim'
    intro ⟨i, h⟩
    pintro
    papply exists_intro i; simp
    papply and_intro
    · pexact lt_ofNat h
    · passumption

end Q

open Q

/-- Peano arithmetic. -/
inductive PA : peano.Theory where
| ax_succ_ne_zero : PA (∀' (~ S #0 ≐ 0))
| ax_succ_inj : PA (∀' ∀' ((S #1 ≐ S #0) ⇒ #1 ≐ #0))
| ax_add_zero : PA (∀' (#0 + 0 ≐ #0))
| ax_add_succ : PA (∀' ∀' (#1 + S #0 ≐ S (#1 + #0)))
| ax_mul_zero : PA (∀' (#0 * 0 ≐ 0))
| ax_mul_succ : PA (∀' ∀' (#1 * S #0 ≐ #1 * #0 + #1))
| ax_ind {n} {p : peano.Formula (n + 1)} : PA (∀* (p[↦ₛ 0]ₚ ⇒ (∀' (p ⇒ p[≔ₛ S #0]ₚ)) ⇒ ∀' p))

namespace PA

theorem ind : ↑ᵀ^[n] PA ⊢ p[↦ₛ 0]ₚ ⇒ (∀' (p ⇒ p[≔ₛ S #0]ₚ)) ⇒ ∀' p := by
  have := foralls_elim .id (hyp (ax_ind (p := p)))
  simp [Formula.subst_id] at this; exact this

theorem zero_or_succ (t) : ↑ᵀ^[n] PA ⊢ t ≐ 0 ⩒ ∃' (↑ₜt ≐ S #0) := by
  psuffices ∀' (#0 ≐ 0 ⩒ ∃' (#1 ≐ S #0))
  · papply forall_elim t at 0
    simp; passumption
  · papply ind <;> simp
    · papply or_inl; prefl
    · pintros 2
      papply or_inr
      papply exists_intro #0; simp
      prefl

instance : Q ⊆ᵀ PA where
  subtheory _ h := by
    cases h with
    | ax_zero_or_succ => pintro; pexact zero_or_succ #0
    | _ => apply hyp; constructor

instance [h : PA ⊆ᵀ T] : Q ⊆ᵀ T := h.trans' inferInstance

lemma zero_add (t) : ↑ᵀ^[n] PA ⊢ 0 + t ≐ t := by
  psuffices ∀' (0 + #0 ≐ #0)
  · papply forall_elim t at 0
    simp; passumption
  · papply ind <;> simp
    · prw [add_zero]; prefl
    · pintros; prw [add_succ, 0]; prefl

lemma succ_add (t₁ t₂) : ↑ᵀ^[n] PA ⊢ S t₁ + t₂ ≐ S (t₁ + t₂) := by
  psuffices ∀' (S ↑ₜt₁ + #0 ≐ S (↑ₜt₁ + #0))
  · papply forall_elim t₂ at 0
    simp; passumption
  · papply ind <;> simp
    · prw [add_zero]; prefl
    · pintros; prw [add_succ, 0]; prefl

theorem add_comm (t₁ t₂) : ↑ᵀ^[n] PA ⊢ t₁ + t₂ ≐ t₂ + t₁ := by
  psuffices ∀' (↑ₜt₁ + #0 ≐ #0 + ↑ₜt₁)
  · papply forall_elim t₂ at 0
    simp; passumption
  · papply ind <;> simp
    · prw [zero_add, add_zero]; prefl
    · pintros; prw [add_succ, 0, succ_add]; prefl

theorem add_assoc (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ + (t₂ + t₃) ≐ t₁ + t₂ + t₃ := by
  psuffices ∀' (↑ₜt₁ + (↑ₜt₂ + #0) ≐ ↑ₜt₁ + ↑ₜt₂ + #0)
  · papply forall_elim t₃ at 0
    simp; passumption
  · papply ind <;> simp
    · prw [add_zero]; prefl
    · pintros; prw [add_succ, add_succ, 0]; prefl

theorem add_right_comm (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ + t₂ + t₃ ≐ t₁ + t₃ + t₂ := by
  prw [←add_assoc t₁ t₂ t₃, add_comm t₂ t₃, add_assoc]
  prefl

theorem add_right_cancel (t) : ↑ᵀ^[n] PA ⊢ t₁ + t ≐ t₂ + t ⇒ t₁ ≐ t₂ := by
  psuffices ∀' (↑ₜt₁ + #0 ≐ ↑ₜt₂ + #0 ⇒ ↑ₜt₁ ≐ ↑ₜt₂)
  · papply forall_elim t at 0
    simp; passumption
  · papply ind <;> simp
    · prw [add_zero]; pexact identity
    · pintro
      prw [add_succ]
      pintros
      papplya 1
      papply succ_inj
      passumption

theorem add_left_cancel (t) : ↑ᵀ^[n] PA ⊢ t + t₁ ≐ t + t₂ ⇒ t₁ ≐ t₂ := by
  prw [add_comm]
  pexact add_right_cancel t

theorem zero_mul (t) : ↑ᵀ^[n] PA ⊢ 0 * t ≐ 0 := by
  psuffices ∀' (0 * #0 ≐ 0)
  · papply forall_elim t at 0
    simp; passumption
  · papply ind <;> simp
    · prw [mul_zero]; prefl
    · pintros; prw [mul_succ, 0, add_zero]; prefl

theorem succ_mul (t₁ t₂) : ↑ᵀ^[n] PA ⊢ S t₁ * t₂ ≐ t₁ * t₂ + t₂ := by
  psuffices ∀' (S ↑ₜt₁ * #0 ≐ ↑ₜt₁ * #0 + #0)
  · papply forall_elim t₂ at 0
    simp; passumption
  · papply ind <;> simp
    · prw [mul_zero, add_zero]; prefl
    · pintros
      prw [mul_succ, 0, add_succ, add_right_comm _ ↑ₜt₁]
      prefl

theorem mul_comm : ↑ᵀ^[n] PA ⊢ t₁ * t₂ ≐ t₂ * t₁ := by
  psuffices ∀' (↑ₜt₁ * #0 ≐ #0 * ↑ₜt₁)
  · papply forall_elim t₂ at 0
    simp; passumption
  · papply ind <;> simp
    · prw [mul_zero, zero_mul]; prefl
    · pintros; prw [mul_succ, succ_mul, 0]; prefl

theorem right_distrib (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ (t₁ + t₂) * t₃ ≐ t₁ * t₃ + t₂ * t₃ := by
  psuffices ∀' ((↑ₜt₁ + ↑ₜt₂) * #0 ≐ ↑ₜt₁ * #0 + ↑ₜt₂ * #0)
  · papply forall_elim t₃ at 0
    simp; passumption
  · papply ind <;> simp
    · prw [mul_zero, add_zero]; prefl
    · pintros
      prw [mul_succ, 0, add_assoc, add_right_comm (↑ₜt₁ * #0) ↑ₜt₁]
      prefl

theorem left_distrib (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ * (t₂ + t₃) ≐ t₁ * t₂ + t₁ * t₃ := by
  prw [mul_comm, right_distrib]; prefl

theorem mul_assoc (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ * (t₂ * t₃) ≐ t₁ * t₂ * t₃ := by
  psuffices ∀' (↑ₜt₁ * (↑ₜt₂ * #0) ≐ ↑ₜt₁ * ↑ₜt₂ * #0)
  · papply forall_elim t₃ at 0
    simp; passumption
  · papply ind <;> simp
    · prw [mul_zero, mul_zero]; prefl
    · pintros; prw [mul_succ, left_distrib, 0]; prefl

lemma add_eq_zero_right : ↑ᵀ^[n] PA ⊢ t₁ + t₂ ≐ 0 ⇒ t₂ ≐ 0 := by
  prw [add_comm]; pexact add_eq_zero_left

theorem le_refl : ↑ᵀ^[n] PA ⊢ t ⪯ t := by
  papply exists_intro 0; simp
  prw [zero_add]
  prefl

theorem le_antisymm : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₂ ⪯ t₁ ⇒ t₁ ≐ t₂ := by
  papply exists_elim'
  pintros 2
  papply exists_elim'
  pintros 2
  simp; repeat rw [←Term.shift]
  prw [←zero_add ↑ₜ↑ₜt₁, ←1, add_assoc] at 0
  papply add_right_cancel at 0
  papply add_eq_zero_right at 0
  prw [0, zero_add] at 1
  passumption

theorem le_trans : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₂ ⪯ t₃ ⇒ t₁ ⪯ t₃ := by
  papply exists_elim'
  pintros 2
  papply exists_elim'
  pintros 2
  papply exists_intro (#0 + #1)
  simp; repeat rw [←Term.shift]
  prw [←add_assoc, 1, 0]
  prefl

theorem lt_iff_le_not_le : ↑ᵀ^[n] PA ⊢ t₁ ≺ t₂ ⇔ t₁ ⪯ t₂ ⩑ ~ t₂ ⪯ t₁ := by
  papply iff_intro
  · papply exists_elim'
    pintros 2; simp
    papply and_intro
    · papply exists_intro (S #0); simp
      prw [succ_add, ←add_succ, 0]
      prefl
    · papply exists_elim'; simp
      pintros; simp
      prw [←zero_add ↑ₜ↑ₜt₂, ←0, add_succ, ←succ_add, add_assoc, succ_add] at 1
      papply add_right_cancel at 1
      papply succ_ne_zero
      passumption
  · prw [and_imp_iff]
    papply exists_elim'; simp
    pintros 3
    papply or_elim
    · pexact zero_or_succ #0
    · pintro
      papply false_elim
      papplya 1
      prw [←2, 0, zero_add]
      pexact le_refl
    · papply exists_elim'; simp
      pintros 2
      papply exists_intro #0; simp
      prw [←2, 0, add_succ, succ_add]
      prefl

instance : PO ⊆ᵀ PA where
  subtheory _ h := by
    cases h with
    | ax_le_refl => pintro; pexact le_refl
    | ax_le_antisymm => pintros 2; pexact le_antisymm
    | ax_le_trans => pintros 3; pexact le_trans
    | ax_lt_iff_le_not_le => pintros 2; pexact lt_iff_le_not_le

theorem lt_succ_self : ↑ᵀ^[n] PA ⊢ t ≺ S t := by
  prw [lt_succ_iff]
  pexact le_refl

theorem le_succ_self : ↑ᵀ^[n] PA ⊢ t ⪯ S t := by
  papply PO.le_of_lt
  pexact lt_succ_self

theorem le_total : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⩒ t₂ ⪯ t₁ := by
  psuffices ∀' (#0 ⪯ ↑ₜt₂ ⩒ ↑ₜt₂ ⪯ #0)
  · papply forall_elim t₁ at 0; simp
    passumption
  papply ind <;> simp
  · papply or_inl; pexact zero_le
  · pintro
    papply or_elim'
    · prw [PO.le_iff_lt_or_eq (t₁ := #0)]
      papply or_elim'
      · pintro; papply or_inl; simp [lt_def]; passumption
      · pintro; papply or_inr; prw [0]; pexact le_succ_self
    · pintro
      papply or_inr
      papply le_trans
      · passumption
      · pexact le_succ_self

instance : LO ⊆ᵀ PA where
  subtheory _ h := by
    cases h with
    | po h => exact Subtheory.subtheory _ h
    | ax_le_total => pintros 2; pexact le_total

theorem le_succ_iff : ↑ᵀ^[n] PA ⊢ t₁ ⪯ S t₂ ⇔ t₁ ⪯ t₂ ⩒ t₁ ≐ S t₂ := by
  papply iff_intro
  · papply exists_elim'
    pintros 2; simp
    papply or_elim
    · pexact zero_or_succ #0
    · pintro
      papply or_inr
      prw [←1, 0, zero_add]
      prefl
    · papply exists_elim'
      pintros 2; simp
      papply or_inl
      papply exists_intro #0; simp
      papply succ_inj
      prw [←succ_add, ←0, 1]
      prefl
  · papply or_elim'
    · papply exists_elim'; simp
      pintros 2
      papply exists_intro (S #0); simp
      prw [succ_add, 0]
      prefl
    · pintro
      prw [0]
      pexact le_refl

theorem add_le_add : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₃ ⪯ t₄ ⇒ t₁ + t₃ ⪯ t₂ + t₄ := by
  papply exists_elim'
  pintros 2; simp
  papply exists_elim'
  pintros 2; simp
  papply exists_intro (#0 + #1); simp
  prw [add_assoc, ←add_assoc #0, 1, add_right_comm, 0]
  pexact add_comm

/-- Strong induction principle formalized within PA. -/
theorem strong_ind : 
  ↑ᵀ^[n] PA ⊢ ∀' (∀' (#0 ≺ #1 ⇒ p[#0 ∷ᵥ λ i => #(i.addNat 2)]ₚ) ⇒ p) ⇒ ∀' p := by
  pintro
  psuffices ∀' ∀' (#0 ≺ #1 ⇒ p[#0 ∷ᵥ λ i => #(i.addNat 2)]ₚ)
  · pintros
    papply forall_elim (S #0) at 0
    papply forall_elim #0 at 0
    simp [←Formula.subst_comp, Subst.comp_def]; simp_vec
    nth_rw 4 [←Formula.subst_id p]; rw [Vec.eq_cons Subst.id]
    papplya 0
    pexact lt_succ_self
  · papply ind <;> simp [←Formula.subst_comp, Subst.comp_def] <;> simp_vec
    · pintros
      papply false_elim
      papply not_lt_zero
      passumption 0
    · pintros
      simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def]; simp_vec
      papply forall_elim #0 at 2
      simp [←Formula.subst_comp, Subst.comp_def]; simp_vec
      papplya 2
      pintros
      simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def]; simp_vec
      papply forall_elim #0 at 2
      simp [←Formula.subst_comp, Subst.comp_def]; simp_vec
      papplya 2
      papply PO.lt_of_lt_of_le
      · passumption 0
      · prw [lt_succ_iff] at 1
        passumption 1

/-- Least number principle formalized in PA. -/
theorem exists_min :
  ↑ᵀ^[n] PA ⊢ ∃' p ⇒ ∃' (p ⩑ ∀' (#0 ≺ #1 ⇒ ~ p[#0 ∷ᵥ λ i => #(i.addNat 2)]ₚ)) := by
  papply imp_contra
  prw [neg_exists_iff]
  pintro
  papply strong_ind
  pintros
  papply forall_elim #0 at 2
  simp [←Formula.subst_comp, Subst.comp_def]; simp_vec
  papplya 2
  papply and_intro
  · nth_rw 4 [←Formula.subst_id p]; rw [Vec.eq_cons Subst.id]
    passumption
  · passumption

end FirstOrder.Language.Theory.PA
