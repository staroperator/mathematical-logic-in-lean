import MathematicalLogic.FirstOrder.Proof

/-!

# Theory of orders

This file formalizes the basic theories of orders -- the theory of paritial order `PO` and the
theory of linear (total) order `LO`.

## Design note

We always use less-equal `⪯` and less-than `≺` for orders, and do not define greater-equal `⪰` or
greater-than `≻`. When naming the theorems, we may use `ge` or `gt` when it is actually `le` or
`lt`, e.g. `LO.lt_or_ge` is the `lt_or_le` in Mathlib -- we are more comfortable to such names.

-/

namespace FirstOrder.Language

/-- Language with two formulas that represent less-equal `⪯` and less-than `≺`. -/
class Order (L : Language) where
  leDef : L.Formula 2
  ltDef : L.Formula 2

variable {L : Language} [Order L] {t t₁ t₂ t₃ : L.Term n}

namespace Order

def le (t₁ t₂ : L.Term n) := leDef[[t₁, t₂]ᵥ]ₚ
infix:60 " ⪯ " => le
@[simp] theorem subst_le : (t₁ ⪯ t₂)[σ]ₚ = t₁[σ]ₜ ⪯ t₂[σ]ₜ := by
  simp [le, ←Formula.subst_comp]
@[simp] theorem shift_le : ↑ₚ(t₁ ⪯ t₂) = ↑ₜt₁ ⪯ ↑ₜt₂ := subst_le

def lt (t₁ t₂ : L.Term n) := ltDef[[t₁, t₂]ᵥ]ₚ
infix:60 " ≺ " => lt
@[simp] theorem subst_lt : (t₁ ≺ t₂)[σ]ₚ = t₁[σ]ₜ ≺ t₂[σ]ₜ := by
  simp [lt, ←Formula.subst_comp]
@[simp] theorem shift_lt : ↑ₚ(t₁ ≺ t₂) = ↑ₜt₁ ≺ ↑ₜt₂ := subst_lt

/-- Bounded forall. -/
def bdall (t : L.Term n) (p : L.Formula (n + 1)) := ∀' (#0 ≺ ↑ₜt ⇒ p)
notation:100 "∀[" "≺ " t "] " p:100 => bdall t p
@[simp] theorem subst_bdall : (∀[≺ t] p)[σ]ₚ = ∀[≺ t[σ]ₜ] p[⇑ₛσ]ₚ := by
  simp [bdall, Term.shift_subst_lift]

/-- Bounded exists. -/
def bdex (t : L.Term n) (p : L.Formula (n + 1)) := ∃' (#0 ≺ ↑ₜt ⩑ p)
notation "∃[" "≺ " t "] " p:100 => bdex t p
@[simp] theorem subst_bdex : (∃[≺ t] p)[σ]ₚ = ∃[≺ t[σ]ₜ] p[⇑ₛσ]ₚ := by
  simp [bdex, Term.shift_subst_lift]

open Proof

@[prw] theorem iff_congr_le : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ (t₁ ⪯ t₂ ⇔ t₁' ⪯ t₂') := by
  pintros 2; simp [Order.le]; prw [0, 1]; prefl

@[prw] theorem iff_congr_lt : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ (t₁ ≺ t₂ ⇔ t₁' ≺ t₂') := by
  pintros 2; simp [Order.lt]; prw [0, 1]; prefl

@[prw] theorem iff_congr_bdall : Γ ⊢ t₁ ≐ t₂ ⇒ (∀[≺ t₁] p ⇔ ∀[≺ t₂] p) := by
  pintro; papply iff_congr_forall; pintro; simp; prw [0]; prefl

@[prw] theorem iff_congr_bdex : Γ ⊢ t₁ ≐ t₂ ⇒ (∃[≺ t₁] p ⇔ ∃[≺ t₂] p) := by
  pintro; papply iff_congr_exists; pintro; simp; prw [0]; prefl

theorem neg_bdall_iff : ↑ᵀ^[n] LO ⊢ ~ ∀[≺ t] p ⇔ ∃[≺ t] (~ p) := by
  simp [Order.bdall, Order.bdex]
  prw [neg_forall_iff]
  papply iff_congr_exists
  pintro
  prw [neg_imp_iff]
  prefl

theorem neg_bdex_iff : ↑ᵀ^[n] LO ⊢ ~ ∃[≺ t] p ⇔ ∀[≺ t] (~ p) := by
  simp [Order.bdall, Order.bdex]
  prw [neg_exists_iff]
  papply iff_congr_forall
  pintro
  prw [neg_and_iff, imp_iff]
  prefl

end Order

private inductive order.Rel : ℕ → Type where
| le : Rel 2
| lt : Rel 2

/--
  The language of order, with only two binary predicates, `⪯` and `≺`. This is the minimal language
  (or the free language) satisfying `Order`. -/
def order : Language where
  Func _ := Empty
  Rel := order.Rel

instance : Order order where
  leDef := .le ⬝ʳ [#0, #1]ᵥ
  ltDef := .lt ⬝ʳ [#0, #1]ᵥ

namespace Theory

open Proof

/-- Theory of partial order. -/
inductive PO : L.Theory where
| ax_le_refl : PO (∀' (#0 ⪯ #0))
| ax_le_antisymm : PO (∀' ∀' (#1 ⪯ #0 ⇒ #0 ⪯ #1 ⇒ #1 ≐ #0))
| ax_le_trans : PO (∀' ∀' ∀' (#2 ⪯ #1 ⇒ #1 ⪯ #0 ⇒ #2 ⪯ #0))
| ax_lt_iff_le_not_ge : PO (∀' ∀' (#1 ≺ #0 ⇔ #1 ⪯ #0 ⩑ ~ #0 ⪯ #1))

namespace PO

theorem le_refl : ↑ᵀ^[n] PO ⊢ t ⪯ t := by
  have := foralls_elim [t]ᵥ (hyp ax_le_refl)
  simp at this; exact this

theorem le_antisymm : ↑ᵀ^[n] PO ⊢ t₁ ⪯ t₂ ⇒ t₂ ⪯ t₁ ⇒ t₁ ≐ t₂ := by
  have := foralls_elim [t₂, t₁]ᵥ (hyp ax_le_antisymm)
  simp at this; exact this

theorem le_trans : ↑ᵀ^[n] PO ⊢ t₁ ⪯ t₂ ⇒ t₂ ⪯ t₃ ⇒ t₁ ⪯ t₃ := by
  have := foralls_elim [t₃, t₂, t₁]ᵥ (hyp ax_le_trans)
  simp at this; exact this

theorem lt_iff_le_not_ge : ↑ᵀ^[n] PO ⊢ t₁ ≺ t₂ ⇔ t₁ ⪯ t₂ ⩑ ~ t₂ ⪯ t₁ := by
  have := foralls_elim [t₂, t₁]ᵥ (hyp ax_lt_iff_le_not_ge)
  simp at this; exact this

theorem le_of_lt : ↑ᵀ^[n] PO ⊢ t₁ ≺ t₂ ⇒ t₁ ⪯ t₂ := by
  pintro
  prw [lt_iff_le_not_ge] at 0
  papply and_left at 0
  passumption

theorem not_ge_of_lt : ↑ᵀ^[n] PO ⊢ t₁ ≺ t₂ ⇒ ~ t₂ ⪯ t₁ := by
  prw [lt_iff_le_not_ge, and_imp_iff]
  pintros 2
  passumption

theorem not_gt_of_le : ↑ᵀ^[n] PO ⊢ t₁ ⪯ t₂ ⇒ ~ t₂ ≺ t₁ := by
  pintros
  papply not_ge_of_lt <;> passumption

theorem lt_iff_le_and_ne : ↑ᵀ^[n] PO ⊢ t₁ ≺ t₂ ⇔ t₁ ⪯ t₂ ⩑ ~ t₁ ≐ t₂ := by
  prw [lt_iff_le_not_ge]
  papply iff_intro <;> prw [and_imp_iff] <;> pintros 2 <;> papply and_intro
  · passumption
  · pintro
    prw [0] at 1
    papplya 1
    pexact le_refl
  · passumption
  · pintro
    papplya 1
    papply le_antisymm <;> passumption

theorem ne_of_lt : ↑ᵀ^[n] PO ⊢ t₁ ≺ t₂ ⇒ ~ t₁ ≐ t₂ := by
  pintros
  prw [lt_iff_le_and_ne] at 1
  papply and_right at 1
  papplya 1
  passumption

theorem le_iff_lt_or_eq : ↑ᵀ^[n] PO ⊢ t₁ ⪯ t₂ ⇔ t₁ ≺ t₂ ⩒ t₁ ≐ t₂ := by
  papply iff_intro
  · pintros
    pcontra
    papplya 1
    prw [lt_iff_le_and_ne]
    papply and_intro <;> passumption
  · papply or_elim'
    · pexact le_of_lt
    · pintro; prw [0]; pexact le_refl

theorem lt_irrefl : ↑ᵀ^[n] PO ⊢ ~ t ≺ t := by
  prw [lt_iff_le_and_ne, neg_and_iff, double_neg_iff]
  papply or_inr
  prefl

theorem lt_of_lt_of_le : ↑ᵀ^[n] PO ⊢ t₁ ≺ t₂ ⇒ t₂ ⪯ t₃ ⇒ t₁ ≺ t₃ := by
  pintros
  prw [lt_iff_le_and_ne]
  papply and_intro
  · papply le_trans
    · papply le_of_lt
      passumption
    · passumption
  · pintro
    prw [0] at 2
    papply not_ge_of_lt <;> passumption

theorem lt_of_le_of_lt : ↑ᵀ^[n] PO ⊢ t₁ ⪯ t₂ ⇒ t₂ ≺ t₃ ⇒ t₁ ≺ t₃ := by
  pintros
  prw [lt_iff_le_and_ne]
  papply and_intro
  · papply le_trans
    · passumption
    · papply le_of_lt
      passumption
  · pintro
    prw [←0] at 1
    papply not_ge_of_lt <;> passumption

theorem lt_asymm : ↑ᵀ^[n] PO ⊢ t₁ ≺ t₂ ⇒ ~ t₂ ≺ t₁ := by
  pintros
  papply le_of_lt at 1
  papply not_ge_of_lt <;> passumption

theorem lt_trans : ↑ᵀ^[n] PO ⊢ t₁ ≺ t₂ ⇒ t₂ ≺ t₃ ⇒ t₁ ≺ t₃ := by
  pintros
  papply lt_of_lt_of_le
  · passumption
  · papply le_of_lt
    passumption

end PO

open PO

/-- Theory of linear order. -/
inductive LO : L.Theory where
| ax_po : p ∈ PO → LO p
| ax_le_total : LO (∀' ∀' (#1 ⪯ #0 ⩒ #0 ⪯ #1))

namespace LO

instance : PO ⊆ᵀ (LO : L.Theory) := .of_subset (λ _ => ax_po)

instance {T : L.Theory} [h : LO ⊆ᵀ T] : PO ⊆ᵀ T := h.trans' inferInstance

theorem le_total (t₁ t₂ : L.Term n) : ↑ᵀ^[n] LO ⊢ t₁ ⪯ t₂ ⩒ t₂ ⪯ t₁ := by
  have := foralls_elim [t₂, t₁]ᵥ (hyp ax_le_total)
  simp at this; exact this

theorem not_le_iff : ↑ᵀ^[n] LO ⊢ ~ t₁ ⪯ t₂ ⇔ t₂ ≺ t₁ := by
  papply iff_intro
  · pintro
    prw [PO.lt_iff_le_and_ne]
    papply and_intro
    · papply le_total
      passumption
    · pintro
      papplya 1
      prw [0]
      pexact PO.le_refl
  · pexact PO.not_ge_of_lt

theorem not_lt_iff : ↑ᵀ^[n] LO ⊢ ~ t₁ ≺ t₂ ⇔ t₂ ⪯ t₁ := by
  papply iff_intro
  · pintro
    pcontra
    prw [not_le_iff] at 0
    papplya 1
    passumption
  · pexact PO.not_gt_of_le

theorem le_or_gt (t₁ t₂ : L.Term n) : ↑ᵀ^[n] LO ⊢ t₁ ⪯ t₂ ⩒ t₂ ≺ t₁ := by
  papply or_elim
  · pexact le_total t₁ t₂
  · pexact or_inl
  · prw [PO.le_iff_lt_or_eq]
    papply or_elim'
    · pintro
      papply or_inr
      passumption
    · pintro
      papply or_inl
      papply or_inr
      prw [0]
      prefl

theorem lt_or_ge (t₁ t₂ : L.Term n) : ↑ᵀ^[n] LO ⊢ t₁ ≺ t₂ ⩒ t₂ ⪯ t₁ := by
  papply or_elim
  · pexact le_or_gt t₂ t₁
  · pexact or_inr
  · pexact or_inl

theorem lt_trichotomy (t₁ t₂ : L.Term n) : ↑ᵀ^[n] LO ⊢ t₁ ≺ t₂ ⩒ t₁ ≐ t₂ ⩒ t₂ ≺ t₁ := by
  papply or_elim
  · pexact le_or_gt t₁ t₂
  · prw [PO.le_iff_lt_or_eq]
    papply or_elim'
    · pintro
      papply or_inl
      passumption
    · pintro
      papply or_inr
      papply or_inl
      prw [0]
      prefl
  · pintro
    papply or_inr
    papply or_inr
    passumption

end LO

end Theory

end FirstOrder.Language
