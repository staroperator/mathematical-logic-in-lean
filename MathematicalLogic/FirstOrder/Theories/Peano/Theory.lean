import MathematicalLogic.FirstOrder.Theories.Order.Theory

/-!

# Theory of first-order arithmetic

This file formalizes Peano arithmetic and Robinson's Q, two first-order theories of arithmetic. The
goal is to prove Gödel's first incompleteness theorem under `Q` and second incompleteness theorem
under `PA`.

-/

namespace FirstOrder.Language

inductive peanoFunc : ℕ → Type where
| zero : peanoFunc 0
| succ : peanoFunc 1
| add : peanoFunc 2
| mul : peanoFunc 2

/-- The language of first-order arithmetic. -/
def peano : Language where
  Func := peanoFunc
  Rel _ := Empty

variable {t t₁ t₂ t₃ t₄: peano.Term n}

namespace peano

def succ (t : peano.Term n) : peano.Term n := .succ ⬝ᶠ [t]ᵥ
scoped notation "S" => succ

instance : Zero (peano.Term n) := ⟨(.zero ⬝ᶠ []ᵥ)⟩
instance : One (peano.Term n) := ⟨S 0⟩
instance : Add (peano.Term n) := ⟨(.add ⬝ᶠ [·, ·]ᵥ)⟩
instance : Mul (peano.Term n) := ⟨(.mul ⬝ᶠ [·, ·]ᵥ)⟩

def ofNat : ℕ → peano.Term n
| 0 => 0
| n + 1 => S (ofNat n)
instance : Coe ℕ (peano.Term m) := ⟨ofNat⟩

def ofEncode [Encodable α] (a : α) : peano.Term n := ofNat (Encodable.encode a)
scoped notation "⌜" a "⌝" => ofEncode a

@[simp, syntax_simp] theorem zero_eq : (.zero ⬝ᶠ []ᵥ : peano.Term n) = 0 := rfl
@[simp, syntax_simp] theorem succ_eq : (.succ ⬝ᶠ [t₁]ᵥ : peano.Term n) = S t₁ := rfl
@[simp, syntax_simp] theorem add_eq : (.add ⬝ᶠ [t₁, t₂]ᵥ : peano.Term n) = t₁ + t₂ := rfl
@[simp, syntax_simp] theorem mul_eq : (.mul ⬝ᶠ [t₁, t₂]ᵥ : peano.Term n) = t₁ * t₂ := rfl
theorem ofNat_zero : (ofNat 0 : peano.Term n) = 0 := rfl
theorem ofNat_succ : ofNat (a + 1) = S (ofNat a : peano.Term n) := rfl

theorem one_def : (1 : peano.Term n) = S 0 := rfl
@[simp, syntax_simp] theorem ofNat_one : (ofNat 1 : peano.Term n) = 1 := rfl

@[simp, syntax_simp] theorem subst_zero : (0 : peano.Term n)[σ]ₜ = 0 := by
  simp [← zero_eq, Vec.eq_nil]
@[simp, syntax_simp] theorem subst_succ : (S t)[σ]ₜ = S (t[σ]ₜ) := by
  simp [← succ_eq, Vec.eq_one]
@[simp, syntax_simp] theorem subst_one : (1 : peano.Term n)[σ]ₜ = 1 := by
  simp [one_def]
@[simp, syntax_simp] theorem subst_add : (t₁ + t₂)[σ]ₜ = t₁[σ]ₜ + t₂[σ]ₜ := by
  simp [← add_eq, Vec.eq_two]
@[simp, syntax_simp] theorem subst_mul : (t₁ * t₂)[σ]ₜ = t₁[σ]ₜ * t₂[σ]ₜ := by
  simp [← mul_eq, Vec.eq_two]
@[simp, syntax_simp] theorem subst_ofNat : (ofNat n)[σ]ₜ = ofNat n := by
  induction n with simp [*, ofNat]
@[simp, syntax_simp] theorem subst_ofEncode [Encodable α] {a : α} : (⌜a⌝)[σ]ₜ = ⌜a⌝ :=
  subst_ofNat

instance : Order peano where
  leDef := ∃' (#0 + #1 ≐ #2)
  ltDef := ∃' (#0 + S #1 ≐ #2)

theorem le_def : t₁ ⪯ t₂ = ∃' (#0 + ↑ₜt₁ ≐ ↑ₜt₂) := by syntax_simp [Order.le, Order.leDef]

theorem lt_def : t₁ ≺ t₂ = S t₁ ⪯ t₂ := by syntax_simp [Order.lt, Order.ltDef, le_def]

open Proof

@[prw] theorem eq_congr_succ : Γ ⊢ t₁ ≐ t₂ ⇒ S t₁ ≐ S t₂ := by
  pintro; papply eq_congr_func; apply andN_intro; intro i; cases i using Fin.cases1; passumption

@[prw] theorem eq_congr_add : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ + t₂ ≐ t₁' + t₂' := by
  pintros; papply eq_congr_func; apply andN_intro; intro i; cases i using Fin.cases2 <;> passumption

@[prw] theorem eq_congr_mul : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ * t₂ ≐ t₁' * t₂' := by
  pintros; papply eq_congr_func; apply andN_intro; intro i; cases i using Fin.cases2 <;> passumption

open Std Lean.Parser in
instance : Repr peano where
  reprFunc
  | .zero, _, _ => "0"
  | .succ, prec, v => Repr.addAppParen ("S " ++ v 0 argPrec) prec
  | .add, prec, v => (if prec ≥ 65 then Format.paren else id) (v 0 65 ++ " + " ++ v 1 65)
  | .mul, prec, v => (if prec ≥ 70 then Format.paren else id) (v 0 70 ++ " * " ++ v 1 70)
  reprRel := nofun

end peano

namespace Theory

open peano Proof

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
  syntax_simp at this
  exact this

theorem succ_inj : ↑ᵀ^[n] Q ⊢ S t₁ ≐ S t₂ ⇒ t₁ ≐ t₂ := by
  have := foralls_elim [t₂, t₁]ᵥ (hyp ax_succ_inj)
  syntax_simp at this
  exact this

theorem add_zero (t) : ↑ᵀ^[n] Q ⊢ t + 0 ≐ t := by
  have := foralls_elim [t]ᵥ (hyp ax_add_zero)
  syntax_simp at this
  exact this

theorem add_succ (t₁ t₂) : ↑ᵀ^[n] Q ⊢ t₁ + S t₂ ≐ S (t₁ + t₂) := by
  have := foralls_elim [t₂, t₁]ᵥ (hyp ax_add_succ)
  syntax_simp at this
  exact this

theorem add_one (t) : ↑ᵀ^[n] Q ⊢ t + 1 ≐ S t := by
  rw [one_def]
  prw [add_succ, add_zero]
  prefl

theorem mul_zero (t) : ↑ᵀ^[n] Q ⊢ t * 0 ≐ 0 := by
  have := foralls_elim [t]ᵥ (hyp ax_mul_zero)
  syntax_simp at this
  exact this

theorem mul_succ (t₁ t₂) : ↑ᵀ^[n] Q ⊢ t₁ * S t₂ ≐ t₁ * t₂ + t₁ := by
  have := foralls_elim [t₂, t₁]ᵥ (hyp ax_mul_succ)
  syntax_simp at this
  exact this

theorem zero_or_succ (t) : ↑ᵀ^[n] Q ⊢ t ≐ 0 ⩒ ∃' (↑ₜt ≐ S #0) := by
  have := foralls_elim [t]ᵥ (hyp ax_zero_or_succ)
  syntax_simp at this
  exact this

theorem succ_inj_iff : ↑ᵀ^[n] Q ⊢ S t₁ ≐ S t₂ ⇔ t₁ ≐ t₂ := by
  papply iff_intro
  · pexact succ_inj
  · pintro; prw [0]; prefl

theorem add_eq_zero_iff : ↑ᵀ^[n] Q ⊢ t₁ + t₂ ≐ 0 ⇔ t₁ ≐ 0 ⩑ t₂ ≐ 0 := by
  papply iff_intro
  · pintro
    papply or_elim
    · pexact zero_or_succ t₂
    · pintro
      papply and_intro
      · prw [0, add_zero] at 1; passumption
      · passumption
    · papply exists_elim'
      pintros 2
      syntax_simp
      prw [0, add_succ] at 1
      papply succ_ne_zero at 1
      papply false_elim
      passumption
  · prw [and_imp_iff]; pintros 2; prw [0, 1, add_zero]; prefl

theorem le_of_add_eq : ↑ᵀ^[n] Q ⊢ t₁ + t₂ ≐ t₃ ⇒ t₂ ⪯ t₃ := by
  pintro
  papply exists_intro t₁
  syntax_simp
  passumption

theorem zero_le : ↑ᵀ^[n] Q ⊢ 0 ⪯ t := by
  papply exists_intro t
  syntax_simp
  pexact add_zero

theorem succ_not_le_zero : ↑ᵀ^[n] Q ⊢ ~ S t ⪯ 0 := by
  pintro
  papply exists_elim
  · passumption 0
  · pintro
    syntax_simp
    prw [add_succ]
    pexact succ_ne_zero

theorem le_zero_iff_eq_zero : ↑ᵀ^[n] Q ⊢ t ⪯ 0 ⇔ t ≐ 0 := by
  papply iff_intro
  · papply exists_elim'
    pintros
    syntax_simp
    prw [add_eq_zero_iff] at 0
    papply and_right at 0
    passumption
  · pintro
    prw [0]
    pexact zero_le

theorem succ_le_iff_lt : ↑ᵀ^[n] Q ⊢ S t₁ ⪯ t₂ ⇔ t₁ ≺ t₂ := by
  rw [lt_def]; prefl

theorem one_le_iff_zero_lt : ↑ᵀ^[n] Q ⊢ 1 ⪯ t ⇔ 0 ≺ t := by
  rw [one_def]; prw [succ_le_iff_lt]; prefl

theorem succ_le_succ_iff : ↑ᵀ^[n] Q ⊢ S t₁ ⪯ S t₂ ⇔ t₁ ⪯ t₂ := by
  papply iff_intro
  · papply exists_elim'
    pintros 2
    papply exists_intro #0
    syntax_simp
    papply succ_inj
    prw [← 0, add_succ]
    prefl
  · papply exists_elim'
    pintros 2
    papply exists_intro #0
    syntax_simp
    prw [← 0, add_succ]
    prefl

theorem not_lt_zero : ↑ᵀ^[n] Q ⊢ ~ t ≺ 0 := by
  rw [lt_def]
  pexact succ_not_le_zero

theorem lt_succ_iff_le : ↑ᵀ^[n] Q ⊢ t₁ ≺ S t₂ ⇔ t₁ ⪯ t₂ := by
  rw [lt_def]
  pexact succ_le_succ_iff

theorem succ_lt_succ_iff : ↑ᵀ^[n] Q ⊢ S t₁ ≺ S t₂ ⇔ t₁ ≺ t₂ := by
  rw [lt_def, lt_def]
  pexact succ_le_succ_iff

theorem zero_lt_succ : ↑ᵀ^[n] Q ⊢ 0 ≺ S t := by
  prw [lt_succ_iff_le]
  pexact zero_le

variable {a b : ℕ}

theorem add_ofNat : ↑ᵀ^[n] Q ⊢ a + b ≐ (a + b : ℕ) := by
  induction b with simp only [ofNat]
  | zero => apply add_zero
  | succ b ih => prw [add_succ, ih]; prefl

theorem mul_ofNat : ↑ᵀ^[n] Q ⊢ a * b ≐ (a * b : ℕ) := by
  induction b with simp only [ofNat]
  | zero => apply mul_zero
  | succ b ih => prw [mul_succ, ih, add_ofNat]; prefl

theorem add_assoc_ofNat : ↑ᵀ^[n] Q ⊢ t₁ + t₂ + a ≐ t₁ + (t₂ + a) := by
  induction a with simp only [ofNat]
  | zero => prw [add_zero]; prefl
  | succ a ih => prw [add_succ, ih, add_succ]; prefl

theorem add_ofNat_cancel : ↑ᵀ^[n] Q ⊢ t₁ + a ≐ t₂ + a ⇒ t₁ ≐ t₂ := by
  induction a with simp only [ofNat]
  | zero => pintro; prw [add_zero] at 0; passumption
  | succ a ih => pintro; prw [add_succ, succ_inj_iff] at 0; papply ih; passumption

theorem ne_ofNat (h : a ≠ b) : ↑ᵀ^[n] Q ⊢ ~ a ≐ b := by
  induction b generalizing a with
  | zero =>
    cases a with
    | zero => simp at h
    | succ a => pexact succ_ne_zero
  | succ b ih =>
    cases a with simp only [ofNat]
    | zero =>
      prw [Proof.ne_comm]
      pexact succ_ne_zero
    | succ a =>
      simp only [ne_eq, Nat.add_right_cancel_iff] at h
      prw [succ_inj_iff]
      exact ih h

theorem le_ofNat (h : a ≤ b) : ↑ᵀ^[n] Q ⊢ a ⪯ b := by
  papply exists_intro (b - a)
  syntax_simp
  prw [add_ofNat]
  rw [Nat.sub_add_cancel h]
  prefl

theorem lt_ofNat (h : a < b) :↑ᵀ^[n] Q ⊢ a ≺ b := by
  rw [lt_def]
  exact le_ofNat h

theorem not_le_ofNat (h : b < a) : ↑ᵀ^[n] Q ⊢ ~ a ⪯ b := by
  induction b generalizing a with simp only [ofNat]
  | zero =>
    cases a with
    | zero => simp at h
    | succ => pexact succ_not_le_zero
  | succ b ih =>
    cases a with simp only [ofNat]
    | zero =>
      simp at h
    | succ =>
      simp only [Nat.add_lt_add_iff_right] at h
      prw [succ_le_succ_iff]
      exact ih h

theorem not_lt_ofNat (h : b ≤ a) : ↑ᵀ^[n] Q ⊢ ~ a ≺ b := by
  rw [lt_def]
  exact not_le_ofNat (Nat.lt_succ_of_le h)

theorem add_le_add_ofNat_iff : ↑ᵀ^[n] Q ⊢ t₁ + a ⪯ t₂ + a ⇔ t₁ ⪯ t₂ := by
  induction a with simp only [ofNat]
  | zero => prw [add_zero]; prefl
  | succ a ih => prw [add_succ, succ_le_succ_iff, ih]; prefl

theorem add_lt_add_ofNat_iff : ↑ᵀ^[n] Q ⊢ t₁ + a ≺ t₂ + a ⇔ t₁ ≺ t₂ := by
  induction a with simp only [ofNat]
  | zero => prw [add_zero]; prefl
  | succ a ih => prw [add_succ, succ_lt_succ_iff, ih]; prefl

theorem eq_or_ge_ofNat (t) (a : ℕ) : ↑ᵀ^[n] Q ⊢ (⋁ (i : Fin a), t ≐ i) ⩒ a ⪯ t := by
  induction a generalizing n t with simp only [ofNat]
  | zero =>
    papply or_inr
    pexact zero_le
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
        papply or_inl
        syntax_simp
        papply orN_intro i.succ
        rw [Fin.val_succ, ofNat_succ]
        prw [1, succ_inj_iff]
        passumption
      · pintro
        papply or_inr
        syntax_simp
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

theorem le_or_gt_ofNat (t) (a : ℕ) : ↑ᵀ^[n] Q ⊢ t ⪯ a ⩒ a ≺ t := by
  prw [←lt_succ_iff_le]
  rw [← ofNat_succ]
  nth_rw 2 [lt_def]
  exact lt_or_ge_ofNat t (a + 1)

theorem lt_ofNat_iff : ↑ᵀ^[n] Q ⊢ t ≺ a ⇔ ⋁ (i : Fin a), t ≐ i := by
  papply iff_intro
  · pintro
    papply or_elim
    · pexact eq_or_ge_ofNat t a
    · pintro; passumption
    · papply exists_elim'
      pintros
      syntax_simp
      nth_rw 1 [← Nat.zero_add a]
      prw [← 0, ← add_ofNat, add_lt_add_ofNat_iff] at 1
      papply not_lt_zero at 1
      papply false_elim
      passumption
  · papply orN_elim'
    intro ⟨i, h⟩
    pintro
    prw [0]
    pexact lt_ofNat h

theorem le_ofNat_iff : ↑ᵀ^[n] Q ⊢ t ⪯ a ⇔ ⋁ (i : Fin (a + 1)), t ≐ i := by
  prw [←lt_succ_iff_le]
  rw [← ofNat_succ]
  prw [lt_ofNat_iff]
  prefl

theorem not_lt_ofNat_iff : ↑ᵀ^[n] Q ⊢ ~ t ≺ a ⇔ a ⪯ t := by
  papply iff_intro
  · pexact lt_or_ge_ofNat t a
  · pintro
    prw [lt_ofNat_iff, neg_orN_iff]
    apply andN_intro
    intro ⟨i, h⟩
    pintro
    prw [0] at 1
    papply not_le_ofNat h at 1
    passumption

theorem not_le_ofNat_iff : ↑ᵀ^[n] Q ⊢ ~ t ⪯ a ⇔ a ≺ t := by
  rw [lt_def]
  prw [←lt_succ_iff_le]
  rw [← ofNat_succ]
  prw [not_lt_ofNat_iff, lt_succ_iff_le]
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
      rw [Nat.lt_succ_iff_lt_or_eq] at h
      rcases h with h | rfl
      · papply or_inl
        prw [0]
        pexact lt_ofNat h
      · papplya 1 at 0
        papply false_elim
        passumption
    · pexact or_inr
  · papply or_elim' <;> pintros <;> prw [0] at 1 <;> papply not_lt_ofNat (le_refl a) at 1 <;> passumption

theorem not_ge_ofNat_iff : ↑ᵀ^[n] Q ⊢ ~ a ⪯ t ⇔ t ≺ a := by
  prw [←not_lt_ofNat_iff, double_neg_iff]; prefl

theorem not_gt_ofNat_iff : ↑ᵀ^[n] Q ⊢ ~ a ≺ t ⇔ t ⪯ a := by
  prw [←not_le_ofNat_iff, double_neg_iff]; prefl

theorem bdall_ofNat_iff : ↑ᵀ^[n] Q ⊢ ∀[≺ a] p ⇔ ⋀ (i : Fin a), p[↦ₛ i]ₚ := by
  papply iff_intro
  · pintro
    apply andN_intro
    intro ⟨i, h⟩
    papply forall_elim i at 0
    syntax_simp
    papplya 0
    pexact lt_ofNat h
  · pintros
    syntax_simp
    prw [lt_ofNat_iff] at 0
    papply orN_elim
    · passumption
    · intro i
      pintro
      papply andN_elim i at 2
      prw [←0] at 2
      syntax_simp
      passumption

theorem bdex_ofNat_iff : ↑ᵀ^[n] Q ⊢ ∃[≺ a] p ⇔ ⋁ (i : Fin a), p[↦ₛ i]ₚ := by
  papply iff_intro
  · papply exists_elim'
    pintro
    syntax_simp
    prw [and_imp_iff]
    pintros
    prw [lt_ofNat_iff] at 1
    papply orN_elim
    · passumption
    · intro i
      pintro
      papply orN_intro i
      prw [← 0]
      syntax_simp
      passumption
  · papply orN_elim'
    intro ⟨i, h⟩
    pintro
    papply exists_intro i
    syntax_simp
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
  syntax_simp [Formula.subst_id] at this
  exact this

protected theorem zero_or_succ (t) : ↑ᵀ^[n] PA ⊢ t ≐ 0 ⩒ ∃' (↑ₜt ≐ S #0) := by
  psuffices ∀' (#0 ≐ 0 ⩒ ∃' (#1 ≐ S #0))
  · papply forall_elim t at 0
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
    · papply or_inl; prefl
    · pintros 2
      papply or_inr
      papply exists_intro #0
      syntax_simp
      prefl

instance : Q ⊆ᵀ PA where
  subtheory _ h := by
    cases h with
    | ax_zero_or_succ => pintro; pexact PA.zero_or_succ #0
    | _ => apply hyp; constructor

instance [h : PA ⊆ᵀ T] : Q ⊆ᵀ T := h.trans' inferInstance

lemma zero_add (t) : ↑ᵀ^[n] PA ⊢ 0 + t ≐ t := by
  psuffices ∀' (0 + #0 ≐ #0)
  · papply forall_elim t at 0
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
    · prw [add_zero]; prefl
    · pintros; prw [add_succ, 0]; prefl

lemma succ_add (t₁ t₂) : ↑ᵀ^[n] PA ⊢ S t₁ + t₂ ≐ S (t₁ + t₂) := by
  psuffices ∀' (S ↑ₜt₁ + #0 ≐ S (↑ₜt₁ + #0))
  · papply forall_elim t₂ at 0
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
    · prw [add_zero]; prefl
    · pintros; prw [add_succ, 0]; prefl

theorem add_comm (t₁ t₂) : ↑ᵀ^[n] PA ⊢ t₁ + t₂ ≐ t₂ + t₁ := by
  psuffices ∀' (↑ₜt₁ + #0 ≐ #0 + ↑ₜt₁)
  · papply forall_elim t₂ at 0
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
    · prw [zero_add, add_zero]; prefl
    · pintros; prw [add_succ, 0, succ_add]; prefl

theorem one_add (t) : ↑ᵀ^[n] PA ⊢ 1 + t ≐ S t := by
  prw [add_comm, add_one]; prefl

theorem add_assoc (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ + t₂ + t₃ ≐ t₁ + (t₂ + t₃) := by
  psuffices ∀' (↑ₜt₁ + ↑ₜt₂ + #0 ≐ ↑ₜt₁ + (↑ₜt₂ + #0))
  · papply forall_elim t₃ at 0
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
    · prw [add_zero]; prefl
    · pintros; prw [add_succ, add_succ, 0]; prefl

theorem add_right_comm (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ + t₂ + t₃ ≐ t₁ + t₃ + t₂ := by
  prw [add_assoc t₁ t₂ t₃, add_comm t₂ t₃, add_assoc]
  prefl

theorem add_right_cancel (t) : ↑ᵀ^[n] PA ⊢ t₁ + t ≐ t₂ + t ⇒ t₁ ≐ t₂ := by
  psuffices ∀' (↑ₜt₁ + #0 ≐ ↑ₜt₂ + #0 ⇒ ↑ₜt₁ ≐ ↑ₜt₂)
  · papply forall_elim t at 0
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
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
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
    · prw [mul_zero]; prefl
    · pintros; prw [mul_succ, 0, add_zero]; prefl

theorem succ_mul (t₁ t₂) : ↑ᵀ^[n] PA ⊢ S t₁ * t₂ ≐ t₁ * t₂ + t₂ := by
  psuffices ∀' (S ↑ₜt₁ * #0 ≐ ↑ₜt₁ * #0 + #0)
  · papply forall_elim t₂ at 0
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
    · prw [mul_zero, add_zero]
      prefl
    · pintros
      prw [mul_succ, 0, add_succ, add_right_comm _ ↑ₜt₁]
      prefl

theorem mul_comm (t₁ t₂) : ↑ᵀ^[n] PA ⊢ t₁ * t₂ ≐ t₂ * t₁ := by
  psuffices ∀' (↑ₜt₁ * #0 ≐ #0 * ↑ₜt₁)
  · papply forall_elim t₂ at 0
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
    · prw [mul_zero, zero_mul]; prefl
    · pintros; prw [mul_succ, succ_mul, 0]; prefl

theorem right_distrib (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ (t₁ + t₂) * t₃ ≐ t₁ * t₃ + t₂ * t₃ := by
  psuffices ∀' ((↑ₜt₁ + ↑ₜt₂) * #0 ≐ ↑ₜt₁ * #0 + ↑ₜt₂ * #0)
  · papply forall_elim t₃ at 0
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
    · prw [mul_zero, add_zero]; prefl
    · pintros
      prw [mul_succ, 0, ←add_assoc, add_right_comm (↑ₜt₁ * #0) ↑ₜt₁]
      prefl

theorem left_distrib (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ * (t₂ + t₃) ≐ t₁ * t₂ + t₁ * t₃ := by
  prw [mul_comm, right_distrib]; prefl

theorem mul_assoc (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ * t₂ * t₃ ≐ t₁ * (t₂ * t₃) := by
  psuffices ∀' (↑ₜt₁ * ↑ₜt₂ * #0 ≐ ↑ₜt₁ * (↑ₜt₂ * #0))
  · papply forall_elim t₃ at 0
    syntax_simp
    passumption
  · papply ind <;> syntax_simp
    · prw [mul_zero, mul_zero]; prefl
    · pintros; prw [mul_succ, left_distrib, 0]; prefl

theorem mul_right_comm : ↑ᵀ^[n] PA ⊢ t₁ * t₂ * t₃ ≐ t₁ * t₃ * t₂ := by
  prw [mul_assoc, mul_comm t₂ t₃]; prefl

theorem mul_one (t) : ↑ᵀ^[n] PA ⊢ t * 1 ≐ t := by
  rw [one_def]; prw [mul_succ, mul_zero, zero_add]; prefl

theorem one_mul (t) : ↑ᵀ^[n] PA ⊢ 1 * t ≐ t := by
  prw [mul_comm, mul_one]; prefl

theorem mul_eq_zero_iff : ↑ᵀ^[n] PA ⊢ t₁ * t₂ ≐ 0 ⇔ t₁ ≐ 0 ⩒ t₂ ≐ 0 := by
  papply iff_intro
  · pintro
    papply or_elim
    · pexact zero_or_succ t₁
    · pexact or_inl
    · papply exists_elim'
      pintros 2
      syntax_simp
      papply or_elim
      · pexact zero_or_succ ↑ₜt₂
      · pexact or_inr
      · papply exists_elim'
        pintros 2
        syntax_simp
        prw [0, 1, mul_succ, add_succ] at 2
        papply succ_ne_zero at 2
        papply false_elim
        passumption
  · papply or_elim' <;> pintro
    · prw [0, zero_mul]; prefl
    · prw [0, mul_zero]; prefl

theorem mul_eq_one_iff : ↑ᵀ^[n] PA ⊢ t₁ * t₂ ≐ 1 ⇔ t₁ ≐ 1 ⩑ t₂ ≐ 1 := by
  papply iff_intro
  · pintro
    papply or_elim
    · pexact zero_or_succ t₁
    · pintro
      prw [0, zero_mul, Proof.eq_comm] at 1
      papply succ_ne_zero at 1
      papply false_elim
      passumption
    · papply exists_elim'
      pintros 2
      syntax_simp
      papply or_elim
      · pexact zero_or_succ #0
      · pintro
        prw [0] at 1
        rw [←one_def]
        prw [1, one_mul] at 2
        papply and_intro <;> passumption
      · papply exists_elim'
        pintros 2
        syntax_simp
        papply or_elim
        · pexact zero_or_succ ↑ₜ↑ₜt₂
        · pintro
          syntax_simp
          prw [0, mul_zero, Proof.eq_comm] at 3
          papply succ_ne_zero at 3
          papply false_elim
          passumption
        · papply exists_elim'
          pintros 2
          syntax_simp
          prw [1] at 2
          prw [2, 0, succ_mul, add_succ, mul_succ, add_succ, succ_add] at 3
          rw [one_def]
          prw [succ_inj_iff] at 3
          papply succ_ne_zero at 3
          papply false_elim
          passumption
  · prw [and_imp_iff]; pintros 2; prw [0, 1, mul_one]; prefl

protected theorem le_refl : ↑ᵀ^[n] PA ⊢ t ⪯ t := by
  papply exists_intro 0
  syntax_simp
  prw [zero_add]
  prefl

protected theorem le_antisymm : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₂ ⪯ t₁ ⇒ t₁ ≐ t₂ := by
  papply exists_elim'
  pintros 2
  papply exists_elim'
  pintros 2
  syntax_simp
  prw [← zero_add (↑ₜ^[2] t₁), ← 1, ← add_assoc] at 0
  papply add_right_cancel at 0
  prw [add_eq_zero_iff] at 0
  papply and_right at 0
  prw [0, zero_add] at 1
  passumption

protected theorem le_trans : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₂ ⪯ t₃ ⇒ t₁ ⪯ t₃ := by
  papply exists_elim'
  pintros 2
  papply exists_elim'
  pintros 2
  papply exists_intro (#0 + #1)
  syntax_simp
  prw [add_assoc, 1, 0]
  prefl

protected theorem lt_iff_le_not_ge : ↑ᵀ^[n] PA ⊢ t₁ ≺ t₂ ⇔ t₁ ⪯ t₂ ⩑ ~ t₂ ⪯ t₁ := by
  papply iff_intro
  · papply exists_elim'
    pintros 2; simp
    papply and_intro
    · papply exists_intro (S #0)
      syntax_simp
      prw [succ_add, ←add_succ, 0]
      prefl
    · papply exists_elim'
      pintros
      syntax_simp
      prw [← zero_add (↑ₜ^[2] t₂), ← 0, add_succ, ← succ_add, ← add_assoc, succ_add] at 1
      papply add_right_cancel at 1
      papply succ_ne_zero
      passumption
  · prw [and_imp_iff]
    papply exists_elim'
    syntax_simp
    pintros 3
    papply or_elim
    · pexact zero_or_succ #0
    · pintro
      papply false_elim
      papplya 1
      prw [←2, 0, zero_add]
      pexact PA.le_refl
    · papply exists_elim'
      pintros 2
      papply exists_intro #0
      syntax_simp
      prw [←2, 0, add_succ, succ_add]
      prefl

theorem lt_succ_self : ↑ᵀ^[n] PA ⊢ t ≺ S t := by
  prw [lt_succ_iff_le]
  pexact PA.le_refl

theorem le_succ_self : ↑ᵀ^[n] PA ⊢ t ⪯ S t := by
  papply exists_intro 1
  syntax_simp
  prw [one_add]
  prefl

protected theorem le_total : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⩒ t₂ ⪯ t₁ := by
  psuffices ∀' (#0 ⪯ ↑ₜt₂ ⩒ ↑ₜt₂ ⪯ #0)
  · papply forall_elim t₁ at 0
    syntax_simp
    passumption
  papply ind <;> syntax_simp
  · papply or_inl; pexact zero_le
  · pintro
    papply or_elim'
    · papply exists_elim'
      pintros 2
      syntax_simp
      papply or_elim
      · pexact zero_or_succ #0
      · pintro; papply or_inr; prw [←1, 0, zero_add]; pexact le_succ_self
      · papply exists_elim'
        pintros 2
        syntax_simp
        papply or_inl; prw [←1, 0, succ_add, succ_le_succ_iff]
        papply le_of_add_eq
        prefl
    · pintro
      papply or_inr
      papply PA.le_trans
      · passumption
      · pexact le_succ_self

instance : LO ⊆ᵀ PA where
  subtheory _ h := by
    cases h with
    | ax_po h =>
      cases h with
      | ax_le_refl => pintro; pexact PA.le_refl
      | ax_le_antisymm => pintros 2; pexact PA.le_antisymm
      | ax_le_trans => pintros 3; pexact PA.le_trans
      | ax_lt_iff_le_not_ge => pintros 2; pexact PA.lt_iff_le_not_ge
    | ax_le_total => pintros 2; pexact PA.le_total

theorem le_succ_of_le : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₁ ⪯ S t₂ := by
  pintro
  papply PO.le_trans
  · passumption
  · pexact le_succ_self

theorem lt_succ_of_lt : ↑ᵀ^[n] PA ⊢ t₁ ≺ t₂ ⇒ t₁ ≺ S t₂ := by
  rw [lt_def, lt_def]; pexact le_succ_of_le

theorem lt_succ_iff_lt_or_eq : ↑ᵀ^[n] PA ⊢ t₁ ≺ S t₂ ⇔ t₁ ≺ t₂ ⩒ t₁ ≐ t₂ := by
  prw [lt_succ_iff_le]; pexact PO.le_iff_lt_or_eq

theorem succ_not_le_self : ↑ᵀ^[n] PA ⊢ ~ S t ⪯ t := by
  papply PO.not_ge_of_lt
  pexact lt_succ_self

theorem succ_ne_self : ↑ᵀ^[n] PA ⊢ ~ S t ≐ t := by
  pintro
  papply succ_not_le_self
  prw [0]
  pexact PO.le_refl

theorem pos_of_lt : ↑ᵀ^[n] PA ⊢ t₁ ≺ t₂ ⇒ 0 ≺ t₂ := by
  papply PO.lt_of_le_of_lt; pexact zero_le

theorem zero_or_pos (t) : ↑ᵀ^[n] PA ⊢ t ≐ 0 ⩒ 0 ≺ t := by
  papply or_elim
  · pexact zero_or_succ t
  · pexact or_inl
  · papply exists_elim'
    pintros 2
    syntax_simp
    papply or_inr
    prw [0]
    pexact zero_lt_succ

theorem add_le_add : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₃ ⪯ t₄ ⇒ t₁ + t₃ ⪯ t₂ + t₄ := by
  papply exists_elim'
  pintros 2
  syntax_simp
  papply exists_elim'
  pintros 2
  papply exists_intro (#0 + #1)
  syntax_simp
  prw [←add_assoc, add_assoc #0, 1, add_right_comm, 0]
  pexact add_comm

theorem add_le_add_iff_left : ↑ᵀ^[n] PA ⊢ t + t₁ ⪯ t + t₂ ⇔ t₁ ⪯ t₂ := by
  papply iff_intro
  · papply exists_elim'
    pintros 2
    syntax_simp
    prw [add_comm #0, add_assoc] at 0
    papply add_left_cancel at 0
    papply le_of_add_eq
    prw [add_comm]
    passumption
  · pintro
    papply add_le_add
    · pexact PO.le_refl
    · passumption

theorem add_le_add_iff_right : ↑ᵀ^[n] PA ⊢ t₁ + t ⪯ t₂ + t ⇔ t₁ ⪯ t₂ := by
  prw [add_comm, add_le_add_iff_left]; prefl

theorem le_add_of_le_left : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₁ ⪯ t + t₂ := by
  pintro
  prw [←zero_add t₁]
  papply add_le_add
  · pexact zero_le
  · passumption

theorem le_add_of_le_right : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₁ ⪯ t₂ + t := by
  prw [add_comm]; pexact le_add_of_le_left

theorem le_add_left : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ + t₁ := by
  papply le_add_of_le_left; pexact PO.le_refl

theorem le_add_right : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₁ + t₂ := by
  papply le_add_of_le_right; pexact PO.le_refl

theorem add_lt_add_of_le_of_lt : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₃ ≺ t₄ ⇒ t₁ + t₃ ≺ t₂ + t₄ := by
  prw [←succ_le_iff_lt, ←add_succ]; pexact add_le_add

theorem add_lt_add_of_lt_of_le : ↑ᵀ^[n] PA ⊢ t₁ ≺ t₂ ⇒ t₃ ⪯ t₄ ⇒ t₁ + t₃ ≺ t₂ + t₄ := by
  prw [←succ_le_iff_lt, ←succ_add]; pexact add_le_add

theorem add_lt_add_iff_left : ↑ᵀ^[n] PA ⊢ t + t₁ ≺ t + t₂ ⇔ t₁ ≺ t₂ := by
  prw [←succ_le_iff_lt, ←add_succ, add_le_add_iff_left]; prefl

theorem add_lt_add_iff_right : ↑ᵀ^[n] PA ⊢ t₁ + t ≺ t₂ + t ⇔ t₁ ≺ t₂ := by
  prw [←succ_le_iff_lt, ←succ_add, add_le_add_iff_right]; prefl

theorem lt_add_of_lt_left : ↑ᵀ^[n] PA ⊢ t₁ ≺ t₂ ⇒ t₁ ≺ t + t₂ := by
  prw [←succ_le_iff_lt]; pexact le_add_of_le_left

theorem lt_add_of_lt_right : ↑ᵀ^[n] PA ⊢ t₁ ≺ t₂ ⇒ t₁ ≺ t₂ + t := by
  prw [←succ_le_iff_lt]; pexact le_add_of_le_right

theorem lt_add_of_pos_left : ↑ᵀ^[n] PA ⊢ 0 ≺ t ⇒ t₁ ≺ t + t₁ := by
  pintro
  phave 0 + t₁ ≺ t + t₁
  · papply add_lt_add_of_lt_of_le
    · passumption
    · pexact PO.le_refl
  prw [zero_add] at 0
  passumption

theorem lt_add_of_pos_right : ↑ᵀ^[n] PA ⊢ 0 ≺ t ⇒ t₁ ≺ t₁ + t := by
  prw [add_comm]; pexact lt_add_of_pos_left

theorem mul_le_mul : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₃ ⪯ t₄ ⇒ t₁ * t₃ ⪯ t₂ * t₄ := by
  papply exists_elim'
  pintros 2
  syntax_simp
  papply exists_elim'
  pintros 2
  papply exists_intro (#1 * #0 + ↑ₜ↑ₜt₁ * #0 + #1 * ↑ₜ↑ₜt₃)
  syntax_simp
  prw [← 0, ← 1, left_distrib, right_distrib, ← add_assoc]
  prefl

theorem mul_le_mul_left : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t * t₁ ⪯ t * t₂ := by
  pintro
  papply mul_le_mul
  · pexact PO.le_refl
  · passumption

theorem mul_le_mul_right : ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₁ * t ⪯ t₂ * t := by
  prw [mul_comm]; pexact mul_le_mul_left

theorem le_mul_of_le_left : ↑ᵀ^[n] PA ⊢ 0 ≺ t ⇒ t₁ ⪯ t₂ ⇒ t₁ ⪯ t * t₂ := by
  pintros 2
  prw [←one_mul t₁]
  papply mul_le_mul
  · prw [one_le_iff_zero_lt]; passumption
  · passumption

theorem le_mul_of_le_right : ↑ᵀ^[n] PA ⊢ 0 ≺ t ⇒ t₁ ⪯ t₂ ⇒ t₁ ⪯ t₂ * t := by
  prw [mul_comm]; pexact le_mul_of_le_left

theorem le_mul_left : ↑ᵀ^[n] PA ⊢ 0 ≺ t₂ ⇒ t₁ ⪯ t₂ * t₁ := by
  pintro
  papply le_mul_of_le_left
  · passumption
  · pexact PO.le_refl

theorem le_mul_right : ↑ᵀ^[n] PA ⊢ 0 ≺ t₂ ⇒ t₁ ⪯ t₁ * t₂ := by
  prw [mul_comm]; pexact le_mul_left

theorem mul_lt_mul_left : ↑ᵀ^[n] PA ⊢ 0 ≺ t ⇒ t₁ ≺ t₂ ⇒ t * t₁ ≺ t * t₂ := by
  pintros 2
  papply PO.lt_of_le_of_lt'
  · papply mul_le_mul_left
    prw [←succ_le_iff_lt] at 0
    passumption 0
  · prw [mul_succ]
    papply lt_add_of_pos_right
    passumption

theorem mul_lt_mul_right : ↑ᵀ^[n] PA ⊢ 0 ≺ t ⇒ t₁ ≺ t₂ ⇒ t₁ * t ≺ t₂ * t := by
  prw [mul_comm]; pexact mul_lt_mul_left

theorem lt_mul_left : ↑ᵀ^[n] PA ⊢ 0 ≺ t₁ ⇒ 1 ≺ t₂ ⇒ t₁ ≺ t₂ * t₁ := by
  pintros 2
  phave 1 * t₁ ≺ t₂ * t₁
  · papply mul_lt_mul_right <;> passumption
  prw [one_mul] at 0
  passumption

theorem lt_mul_right : ↑ᵀ^[n] PA ⊢ 0 ≺ t₁ ⇒ 1 ≺ t₂ ⇒ t₁ ≺ t₁ * t₂ := by
  prw [mul_comm]; pexact lt_mul_left

theorem mul_le_mul_iff_left : ↑ᵀ^[n] PA ⊢ 0 ≺ t ⇒ t * t₁ ⪯ t * t₂ ⇔ t₁ ⪯ t₂ := by
  pintro
  papply iff_intro
  · pintro
    pcontra
    prw [LO.neg_le_iff] at 0
    papply PO.not_gt_of_le
    · passumption 1
    · papply mul_lt_mul_left <;> passumption
  · pexact mul_le_mul_left

theorem mul_le_mul_iff_right : ↑ᵀ^[n] PA ⊢ 0 ≺ t ⇒ t₁ * t ⪯ t₂ * t ⇔ t₁ ⪯ t₂ := by
  prw [mul_comm]; pexact mul_le_mul_iff_left

theorem mul_pos_iff : ↑ᵀ^[n] PA ⊢ 0 ≺ t₁ * t₂ ⇔ 0 ≺ t₁ ⩑ 0 ≺ t₂ := by
  papply iff_intro
  · pintro
    pcontra
    prw [neg_and_iff, LO.neg_lt_iff, le_zero_iff_eq_zero] at 0
    papply or_elim
    · passumption 0
    · pintro
      prw [0, zero_mul] at 2
      papply not_lt_zero at 2
      passumption
    · pintro
      prw [0, mul_zero] at 2
      papply not_lt_zero at 2
      passumption
  · prw [and_imp_iff]; pintros 2
    prw [←one_le_iff_zero_lt, ←mul_one 1]
    papply mul_le_mul <;> prw [one_le_iff_zero_lt] <;> passumption

/-- Strong induction principle formalized in `PA`. -/
theorem strong_ind : 
  ↑ᵀ^[n] PA ⊢ ∀' (∀[≺ #0] p[#0 ∷ᵥ Subst.shift 2]ₚ ⇒ p) ⇒ ∀' p := by
  pintro
  psuffices ∀' ∀[≺ #0] p[#0 ∷ᵥ Subst.shift 2]ₚ
  · pintros
    papply forall_elim (S #0) at 0
    papply forall_elim #0 at 0
    syntax_simp
    papplya 0
    pexact lt_succ_self
  · papply ind <;> syntax_simp
    · pintros
      syntax_simp
      papply not_lt_zero at 0
      papply false_elim
      passumption
    · pintros
      papply forall_elim #0 at 2
      syntax_simp
      papplya 2
      pintros
      papply forall_elim #0 at 2
      syntax_simp
      papplya 2
      papply PO.lt_of_lt_of_le
      · passumption 0
      · prw [lt_succ_iff_le] at 1
        passumption 1

/-- Least number principle formalized in `PA`. -/
theorem exists_min :
  ↑ᵀ^[n] PA ⊢ ∃' p ⇒ ∃' (p ⩑ ∀[≺ #0] (~ p[#0 ∷ᵥ Subst.shift 2]ₚ)) := by
  papply imp_contra
  prw [neg_exists_iff]
  pintro
  papply strong_ind
  pintros
  papply forall_elim #0 at 2
  syntax_simp
  papplya 2
  papply and_intro <;> passumption

end FirstOrder.Language.Theory.PA
