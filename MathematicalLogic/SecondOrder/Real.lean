import MathematicalLogic.SecondOrder.Semantics
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Sqrt

namespace SecondOrder.Language

inductive OrderedField.Func : ℕ → Type where
| zero : Func 0
| one : Func 0
| add : Func 2
| neg : Func 1
| mul : Func 2

inductive OrderedField.Rel : ℕ → Type where
| le : Rel 2

def OrderedField : Language where
  Func := OrderedField.Func
  Rel := OrderedField.Rel

namespace OrderedField

instance : Zero (OrderedField.Term Γ) := ⟨.zero ⬝ᶠ []ᵥ⟩
instance : One (OrderedField.Term Γ) := ⟨.one ⬝ᶠ []ᵥ⟩
instance : Add (OrderedField.Term Γ) := ⟨(.add ⬝ᶠ [·, ·]ᵥ)⟩
instance : Neg (OrderedField.Term Γ) := ⟨(.neg ⬝ᶠ [·]ᵥ)⟩
instance : Sub (OrderedField.Term Γ) := ⟨(· + -·)⟩
instance : Mul (OrderedField.Term Γ) := ⟨(.mul ⬝ᶠ [·, ·]ᵥ)⟩

def le (t₁ t₂ : OrderedField.Term Γ) : OrderedField.Formula Γ := .le ⬝ʳ [t₁, t₂]ᵥ
scoped infix:60 " ⪁ " => le

end OrderedField

namespace Theory

open OrderedField

inductive Real : OrderedField.Theory where
| ax_add_assoc : Real (∀' (∀' (∀' (#2 + #1 + #0 ≐ #2 + (#1 + #0)))))
| ax_add_comm : Real (∀' (∀' (#1 + #0 ≐ #0 + #1)))
| ax_add_zero : Real (∀' (#0 + 0 ≐ #0))
| ax_add_neg : Real (∀' (#0 + (-#0) ≐ 0))
| ax_mul_assoc : Real (∀' (∀' (∀' (#2 * #1 * #0 ≐ #2 * (#1 * #0)))))
| ax_mul_comm : Real (∀' (∀' (#1 * #0 ≐ #0 * #1)))
| ax_mul_one : Real (∀' (#0 * 1 ≐ #0))
| ax_has_inv : Real (∀' (~ #0 ≐ 0 ⇒ ∃' (#1 * #0 ≐ 1)))
| ax_left_distrib : Real (∀' (∀' (∀' (#2 * (#1 + #0) ≐ #2 * #1 + #2 * #0))))
| ax_zero_ne_one : Real (~ 0 ≐ 1)
| ax_le_refl : Real (∀' (#0 ⪁ #0))
| ax_le_antisymm : Real (∀' (∀' (#1 ⪁ #0 ⇒ #0 ⪁ #1 ⇒ #1 ≐ #0)))
| ax_le_trans : Real (∀' (∀' (∀' (#2 ⪁ #1 ⇒ #1 ⪁ #0 ⇒ #2 ⪁ #0))))
| ax_le_total : Real (∀' (∀' (#1 ⪁ #0 ⩒ #0 ⪁ #1)))
| ax_add_le_add : Real (∀' (∀' (∀' (#2 ⪁ #1 ⇒ #2 + #0 ⪁ #1 + #0))))
| ax_mul_le_mul : Real (∀' (∀' (∀' (#2 ⪁ #1 ⇒ 0 ⪁ #0 ⇒ #2 * #0 ⪁ #1 * #0))))
| ax_exists_lub : Real (∀ʳ 1 (∃' (1 ⬝ʳᵛ [#0]ᵥ) ⇒ ∃' (∀' (2 ⬝ʳᵛ [#0]ᵥ ⇒ #0 ⪁ #1)) ⇒ ∃' (∀' (2 ⬝ʳᵛ [#0]ᵥ ⇒ #0 ⪁ #1) ⩑ ∀' (∀' (3 ⬝ʳᵛ [#0]ᵥ ⇒ #0 ⪁ #1) ⇒ #1 ⪁ #0))))

namespace Real

attribute [local simp] Structure.interp Structure.satisfy Structure.satisfySentence Structure.Assignment.cons Vec.eq_nil Vec.eq_one Vec.eq_two

noncomputable def 𝓡 : Real.Model where
  Dom := ℝ
  interpFunc
  | .zero, _ => 0
  | .one, _ => 1
  | .add, v => v 0 + v 1
  | .neg, v => - v 0
  | .mul, v => v 0 * v 1
  interpRel
  | .le, v => v 0 ≤ v 1
  satisfy_theory p h := by
    cases h with simp [OrderedField.le]
    | ax_add_assoc => apply add_assoc
    | ax_add_comm => apply add_comm
    | ax_mul_assoc => apply mul_assoc
    | ax_mul_comm => apply mul_comm
    | ax_has_inv => intro a h; exists a⁻¹; exact mul_inv_cancel₀ h
    | ax_left_distrib => apply left_distrib
    | ax_le_antisymm => apply le_antisymm
    | ax_le_trans => apply le_trans
    | ax_le_total => apply le_total
    | ax_mul_le_mul => intro a b c; apply mul_le_mul_of_nonneg_right
    | ax_exists_lub =>
      intro R a h₁ b h₂
      exists sSup (R [·]ᵥ)
      exact Real.isLUB_sSup ⟨a, h₁⟩ ⟨b, h₂⟩

variable {𝓜 : Real.Model}

instance : Zero 𝓜 := ⟨𝓜.interpFunc .zero []ᵥ⟩
instance : One 𝓜 := ⟨𝓜.interpFunc .one []ᵥ⟩
instance : Add 𝓜 := ⟨(𝓜.interpFunc .add [·, ·]ᵥ)⟩
instance : Neg 𝓜 := ⟨(𝓜.interpFunc .neg [·]ᵥ)⟩
instance : Mul 𝓜 := ⟨(𝓜.interpFunc .mul [·, ·]ᵥ)⟩

theorem add_comm (a b : 𝓜) : a + b = b + a := by
  have := 𝓜.satisfy_theory _ .ax_add_comm a b
  simp at this; exact this

theorem add_zero (a : 𝓜) : a + 0 = a := by
  have := 𝓜.satisfy_theory _ .ax_add_zero a
  simp at this; exact this

instance : AddCommGroup 𝓜 where
  add_assoc a b c := by
    have := 𝓜.satisfy_theory _ .ax_add_assoc a b c
    simp at this; exact this
  add_comm := add_comm
  zero_add a := by
    rw [add_comm, add_zero]
  add_zero a := add_zero a
  neg_add_cancel a := by
    rw [add_comm (-a) a]
    have := 𝓜.satisfy_theory _ .ax_add_neg a
    simp at this; exact this
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem mul_comm (a b : 𝓜) : a * b = b * a := by
  have := 𝓜.satisfy_theory _ .ax_mul_comm a b
  simp at this; exact this

theorem mul_one (a : 𝓜) : a * 1 = a := by
  have := 𝓜.satisfy_theory _ .ax_mul_one a
  simp at this; exact this

theorem left_distrib (a b c : 𝓜) : a * (b + c) = a * b + a * c := by
  have := 𝓜.satisfy_theory _ .ax_left_distrib a b c
  simp at this; exact this

theorem mul_zero (a : 𝓜) : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  rw [←left_distrib, add_zero, add_zero]

theorem has_inv (a : 𝓜) : a ≠ 0 → ∃ b, a * b = 1 := by
  have := 𝓜.satisfy_theory _ .ax_has_inv a
  simp at this; exact this

open Classical

noncomputable instance : Inv 𝓜 where
  inv a := if h : a = 0 then 0 else Classical.choose (has_inv a h)

noncomputable instance : Field 𝓜 where
  neg_add_cancel := neg_add_cancel
  mul_assoc a b c := by
    have := 𝓜.satisfy_theory _ .ax_mul_assoc a b c
    simp at this; exact this
  mul_comm a b := mul_comm a b
  mul_one a := mul_one a
  one_mul a := by rw [mul_comm, mul_one]
  inv_zero := by simp [Inv.inv]
  mul_inv_cancel a h := by
    simp [Inv.inv, h]
    exact Classical.choose_spec (has_inv a h)
  left_distrib a b c := left_distrib a b c
  right_distrib a b c := by
    rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]
  mul_zero a := mul_zero a
  zero_mul a := by rw [mul_comm, mul_zero]
  exists_pair_ne := by
    exists 0, 1
    have := 𝓜.satisfy_theory _ .ax_zero_ne_one
    simp at this; exact this
  zsmul := zsmulRec
  qsmul := _
  nnqsmul := _

instance : LE 𝓜 := ⟨(𝓜.interpRel .le [·, ·]ᵥ)⟩

noncomputable instance : LinearOrder 𝓜 where
  le_refl a := by
    have := 𝓜.satisfy_theory _ .ax_le_refl a
    simp [OrderedField.le] at this; exact this
  le_antisymm a b := by
    have := 𝓜.satisfy_theory _ .ax_le_antisymm a b
    simp [OrderedField.le] at this; exact this
  le_trans a b := by
    have := 𝓜.satisfy_theory _ .ax_le_trans a b
    simp [OrderedField.le] at this; exact this
  le_total a b := by
    have := 𝓜.satisfy_theory _ .ax_le_total a b
    simp [OrderedField.le] at this; exact this
  decidableLE := _

theorem add_le_add_right (a b c : 𝓜) : a ≤ b → a + c ≤ b + c := by
  have := 𝓜.satisfy_theory _ .ax_add_le_add a b c
  simp [OrderedField.le] at this; exact this

lemma zero_le_neg_iff (a : 𝓜) : 0 ≤ -a ↔ a ≤ 0 := by
  constructor
  · intro h
    apply add_le_add_right _ _ a at h
    rw [zero_add, neg_add_cancel] at h
    exact h
  · intro h
    apply add_le_add_right _ _ (-a) at h
    rw [zero_add, add_neg_cancel] at h
    exact h

theorem mul_le_mul_right (a b c : 𝓜) : a ≤ b → 0 ≤ c → a * c ≤ b * c := by
  have := 𝓜.satisfy_theory _ .ax_mul_le_mul a b c
  simp [OrderedField.le] at this; exact this

noncomputable instance : LinearOrderedField 𝓜 where
  mul_comm := mul_comm
  inv_zero := inv_zero
  mul_inv_cancel a := mul_inv_cancel₀
  qsmul := _
  nnqsmul := _
  decidableLE := _
  le_total := le_total
  add_le_add_left a b h c := by
    rw [add_comm c a, add_comm c b]
    exact add_le_add_right a b c h
  zero_le_one := by
    by_contra h₁
    simp at h₁
    have h₂ : (0 : 𝓜) ≤ -1 := by
      rw [zero_le_neg_iff 1]
      exact le_of_lt h₁
    have h₃ := lt_of_lt_of_le h₁ h₂
    have h₄ := mul_le_mul_right _ _ _ (le_of_lt h₃) h₂
    rw [mul_neg_one, mul_neg_one, neg_neg] at h₄
    have h₅ := h₄.antisymm (le_of_lt h₃)
    simp [h₅] at h₃
  mul_pos a b h₁ h₂ := by
    apply lt_of_le_of_ne
    · have h₃ := mul_le_mul_right _ _ _ (le_of_lt h₁) (le_of_lt h₂)
      rw [zero_mul] at h₃; exact h₃
    · simp [ne_of_gt h₁, ne_of_gt h₂]

theorem exists_lub (s : Set 𝓜) : s.Nonempty → BddAbove s → ∃ u, IsLUB s u := by
  intro ⟨x, h₁⟩ ⟨y, h₂⟩
  have := 𝓜.satisfy_theory _ .ax_exists_lub
  simp [OrderedField.le] at this
  exact this (·.head ∈ s) x h₁ y h₂

noncomputable def ofReal (x : ℝ) : 𝓜 :=
  Classical.choose
    (exists_lub { ↑y | (y : ℚ) (_ : ↑y ≤ x) }
      ((exists_rat_lt x).elim λ y h => ⟨y, y, le_of_lt h, rfl⟩)
      ((exists_rat_gt x).elim λ y h => ⟨y, by
        simp [upperBounds]; intro z; rw [←@Rat.cast_le z y ℝ]; exact (le_of_lt h).trans'⟩))

variable {x y z : ℝ}

theorem ofReal_isLUB : IsLUB { ↑y | (y : ℚ) (_ : ↑y ≤ x) } (@ofReal 𝓜 x) := Classical.choose_spec _

theorem ofReal_rat {q : ℚ} : @ofReal 𝓜 q = q := by
  apply ofReal_isLUB.unique
  constructor
  · intro y; simp; intro z h₁ h₂; simp [←h₂, h₁]
  · intro y h₁; simp [upperBounds] at h₁; exact h₁ q (by rfl)

theorem ofReal_zero : @ofReal 𝓜 0 = 0 := by
  have := @ofReal_rat 𝓜 0
  simp at this; exact this

theorem ofReal_one : @ofReal 𝓜 1 = 1 := by
  have := @ofReal_rat 𝓜 1
  simp at this; exact this

theorem ofReal_lt : @ofReal 𝓜 x < ofReal y ↔ x < y := by
  constructor
  · intro h₁
    simp [isLUB_lt_iff ofReal_isLUB, upperBounds] at h₁
    rcases h₁ with ⟨a, h₁, h₂⟩
    by_contra h₃; simp at h₃
    apply not_lt_of_le _ h₂
    simp [isLUB_le_iff ofReal_isLUB, upperBounds]
    intro s h₄
    apply h₁
    exact h₄.trans h₃
  · intro h₁
    simp [isLUB_lt_iff ofReal_isLUB, upperBounds]
    rcases exists_rat_btwn h₁ with ⟨q, h₂, h₃⟩
    exists q
    constructor
    · intro r h₄
      have := h₄.trans (le_of_lt h₂)
      simp at this; simp [this]
    · simp [lt_isLUB_iff ofReal_isLUB]
      rcases exists_rat_btwn h₃ with ⟨r, h₃, h₄⟩
      simp at h₃
      exists r, le_of_lt h₄

theorem ofReal_le : @ofReal 𝓜 x ≤ ofReal y ↔ x ≤ y := by
  rw [←not_iff_not, not_le, not_le, ofReal_lt]

theorem ofReal_injective : Function.Injective (@ofReal 𝓜) := by
  intro x y h
  apply le_antisymm <;> rw [←ofReal_le, h]

lemma exists_nat_gt (a : 𝓜) : ∃ (n : ℕ), a < n := by
  by_contra h₁
  push_neg at h₁
  let s : Set 𝓜 := { ↑n | (n : ℕ) }
  have h₂ : s.Nonempty := by exists 0; simp [s]
  have h₃ : BddAbove s := by exists a; simp [s, upperBounds]; exact h₁
  rcases exists_lub s h₂ h₃ with ⟨b, h₄⟩
  have h₄ : b ≤ b - 1 := by
    apply h₄.right
    simp [upperBounds, s]
    intro n
    rw [le_sub_iff_add_le, ←Nat.cast_add_one]
    exact h₄.left ⟨n + 1, rfl⟩
  simp at h₄
  exact not_lt_of_ge h₄ zero_lt_one

instance : Archimedean 𝓜 where
  arch x y h := by
    rcases exists_nat_gt (x / y) with ⟨n, h'⟩
    simp [div_lt_iff₀ h] at h'
    exists n
    simp [le_of_lt h']

theorem ofReal_surjective : Function.Surjective (@ofReal 𝓜) := by
  intro a
  let s : Set ℝ := { ↑q | (q : ℚ) (_ : q ≤ a) }
  have h₁ : s.Nonempty := by
    rcases exists_rat_lt a with ⟨q, h₁⟩
    exists q; simp [s]; exact le_of_lt h₁
  have h₂ : BddAbove s := by
    rcases exists_rat_gt a with ⟨q, h₁⟩
    exists q; simp [upperBounds, s]
    intro r h₂
    have := h₂.trans (le_of_lt h₁)
    simp at this; exact this
  exists sSup s
  apply ofReal_isLUB.unique
  constructor
  · simp [upperBounds]
    intro q h₃
    apply le_of_forall_rat_lt_imp_le
    intro r h₄; simp at h₄
    have h₅ := lt_of_lt_of_le (Rat.cast_lt.mpr h₄) h₃
    rw [lt_isLUB_iff (Real.isLUB_sSup h₁ h₂)] at h₅
    rcases h₅ with ⟨_, ⟨r', h₅, h₆⟩, h₇⟩
    subst h₆; simp at h₇
    apply le_trans' h₅
    apply le_of_lt; simp [h₇]
  · intro b h₃
    simp [upperBounds] at h₃
    apply le_of_forall_rat_lt_imp_le
    intro r h₄
    apply h₃
    apply le_csSup h₂
    exists r
    simp [le_of_lt h₄]

theorem ofReal_add : @ofReal 𝓜 (x + y) = ofReal x + ofReal y := by
  apply ofReal_isLUB.unique
  constructor
  · intro z; simp; intro q h₁ h₂; subst h₂
    apply le_of_forall_rat_lt_imp_le
    intro r h₂; simp at h₂
    let δ := (x + y - r) / 2
    have h₃ : 0 < δ := by simp [δ]; exact lt_of_lt_of_le (Rat.cast_lt.mpr h₂) h₁
    rcases exists_rat_btwn (sub_lt_self x h₃) with ⟨r₁, h₄, h₅⟩
    rcases exists_rat_btwn (sub_lt_self y h₃) with ⟨r₂, h₆, h₇⟩
    trans r₁ + r₂
    · have := add_lt_add h₄ h₆
      simp [sub_add_sub_comm, δ, ←Rat.cast_add] at this
      rw [←Rat.cast_add, Rat.cast_le]
      exact le_of_lt this
    · apply add_le_add <;> rw [←ofReal_rat, ofReal_le] <;> apply le_of_lt <;> assumption
  · intro a h₁; simp [upperBounds] at h₁
    apply le_of_forall_rat_lt_imp_le
    intro q h₂
    let δ := (@ofReal 𝓜 x + @ofReal 𝓜 y - q) / 2
    have h₃ : 0 < δ := by simp [δ, h₂]
    rcases exists_rat_btwn (sub_lt_self (ofReal x) h₃) with ⟨r₁, h₄, h₅⟩
    rcases exists_rat_btwn (sub_lt_self (ofReal y) h₃) with ⟨r₂, h₆, h₇⟩
    trans r₁ + r₂
    · have := add_lt_add h₄ h₆
      simp [sub_add_sub_comm, δ, ←Rat.cast_add] at this
      rw [←Rat.cast_add, Rat.cast_le]
      exact le_of_lt this
    · rw [←Rat.cast_add]; apply h₁; simp
      apply add_le_add <;> rw [←@ofReal_le 𝓜, ofReal_rat] <;> apply le_of_lt <;> assumption

theorem ofReal_neg : @ofReal 𝓜 (-x) = -ofReal x := by
  rw [eq_neg_iff_add_eq_zero, ←ofReal_add, neg_add_cancel, ofReal_zero]

lemma exists_sqrt (a : 𝓜) (h : 0 ≤ a) : ∃ b, 0 ≤ b ∧ b ^ 2 = a := by
  let s : Set 𝓜 := { x | 0 ≤ x ∧ x ^ 2 ≤ a }
  have h₁ : s.Nonempty := by exists 0; simp [s, h]
  have h₂ : BddAbove s := by
    rcases exists_nat_gt a with ⟨n, h₂⟩
    have h₃ : 0 < n := by
      have := lt_of_le_of_lt h h₂
      simp at this; exact this
    exists n
    intro b ⟨h₄, h₅⟩
    rw [←pow_le_pow_iff_left₀ (n := 2)]
    · apply h₅.trans; apply (le_of_lt h₂).trans
      apply le_self_pow₀
      · rw [←ofReal_one, ←Rat.cast_natCast, ←ofReal_rat, ofReal_le]
        simp [Nat.succ_le]; exact Nat.pos_of_ne_zero (ne_zero_of_lt h₃)
      · simp
    · exact h₄
    · simp
    · simp
  rcases exists_lub s h₁ h₂ with ⟨b, h₃⟩
  exists b
  have h₄ : 0 ≤ b := by apply h₃.left; simp [s]; exact h
  simp [h₄]
  by_contra h₅
  apply lt_or_gt_of_ne at h₅
  rcases h₅ with h₅ | h₅
  · let δ := min 1 ((a - b ^ 2) / (2 * b + 1))
    have h₆ : 0 < δ := by
      apply lt_min (by simp)
      apply div_pos
      · simp; exact h₅
      · apply lt_of_lt_of_le zero_lt_one; simp; exact h₄
    have h₇ : (b + δ) ^ 2 ≤ a := by
      calc
        (b + δ) ^ 2 = b ^ 2 + δ * (2 * b + δ) := by rw [add_pow_two, mul_add, ←add_assoc, mul_comm δ, pow_two δ]
        _ ≤ b ^ 2 + δ * (2 * b + 1) := by simp [add_le_add_iff_left, mul_le_mul_left h₆]; apply min_le_left
        _ ≤ b ^ 2 + (a - b ^ 2) := by
          rw [add_le_add_iff_left, ←le_div_iff₀]
          · apply min_le_right
          · apply lt_of_lt_of_le zero_lt_one; simp; exact h₄
        _ = a := by simp
    have h₈ : b + δ ∈ s := ⟨add_nonneg h₄ (le_of_lt h₆), h₇⟩
    apply h₃.left at h₈
    simp at h₈
    exact not_lt_of_ge h₈ h₆
  · have h₆ : 0 < b := by
      by_contra h₆; simp at h₆; rw [le_antisymm h₆ h₄] at h₅; simp at h₅; exact not_lt_of_ge h h₅
    let δ := (b ^ 2 - a) / (2 * b)
    have h₇ : 0 < δ := by
      apply div_pos
      · simp; exact h₅
      · simp; exact h₆
    have h₈ : (b - δ) ^ 2 ≥ a := by
      calc
        (b - δ) ^ 2 = b ^ 2 - δ * (2 * b - δ) := by rw [sub_pow_two, mul_sub, ←sub_add, mul_comm δ, pow_two δ]
        _ ≥ b ^ 2 - δ * (2 * b) := by apply sub_le_sub_left; rw [mul_le_mul_left h₇]; simp; exact le_of_lt h₇
        _ ≥ b ^ 2 - (b ^ 2 - a) := by apply sub_le_sub_left; rw [←le_div_iff₀]; simp; exact h₆
        _ = a := by simp
    have h₉ : b - δ ∈ upperBounds s := by
      intro c ⟨h', h''⟩
      apply le_trans' h₈ at h''
      rw [pow_le_pow_iff_left₀] at h''
      · exact h''
      · exact h'
      · simp [δ]; rw [div_le_iff₀]
        · simp [two_mul, mul_add, pow_two, add_assoc]
          exact add_nonneg (mul_nonneg h₄ h₄) h
        · simp; exact h₆
      · simp
    apply h₃.right at h₉
    simp at h₉
    exact not_lt_of_ge h₉ h₇

theorem ofReal_mul {x y} : @ofReal 𝓜 (x * y) = ofReal x * ofReal y := by
  wlog h : 0 < x generalizing x y
  · simp at h
    rcases lt_or_eq_of_le h with h | h
    · apply neg_pos_of_neg at h
      apply this (y := y) at h
      simp [ofReal_neg, neg_mul] at h
      exact h
    · simp [h, ofReal_zero]
  wlog h' : 0 < y generalizing x y
  · simp at h'
    rcases lt_or_eq_of_le h' with h' | h'
    · apply neg_pos_of_neg at h'
      apply this h at h'
      simp [ofReal_neg, neg_mul] at h'
      exact h'
    · simp [h', ofReal_zero]
  apply ofReal_isLUB.unique
  constructor
  · intro z; simp; intro q h₁ h₂; subst h₂
    apply le_of_forall_rat_lt_imp_le
    intro r h₂; simp at h₂
    by_cases h₃ : r > 0
    · let δ := √(x * y / r)
      have h₄ : 1 < δ := by
        simp [δ, Real.lt_sqrt]; rw [lt_div_iff₀]
        · simp; exact lt_of_lt_of_le (Rat.cast_lt.mpr h₂) h₁
        · simp [h₃]
      rcases exists_rat_btwn (div_lt_self h h₄) with ⟨r₁, h₅, h₆⟩
      rcases exists_rat_btwn (div_lt_self h' h₄) with ⟨r₂, h₇, h₈⟩
      trans r₁ * r₂
      · have := mul_lt_mul'' h₅ h₇
          (div_nonneg (le_of_lt h) (le_trans zero_le_one (le_of_lt h₄)))
          (div_nonneg (le_of_lt h') (le_trans zero_le_one (le_of_lt h₄)))
        rw [←mul_div_mul_comm] at this
        simp [δ] at this
        rw [←Real.sqrt_mul, Real.sqrt_mul_self, div_div_cancel₀] at this
        · simp [←Rat.cast_mul] at this
          rw [←Rat.cast_mul, Rat.cast_le]
          exact le_of_lt this
        · simp [ne_of_gt h, ne_of_gt h']
        · apply div_nonneg (mul_nonneg (le_of_lt h) (le_of_lt h'))
          simp; exact le_of_lt h₃
        · apply div_nonneg (mul_nonneg (le_of_lt h) (le_of_lt h'))
          simp; exact le_of_lt h₃
      · apply mul_le_mul
        · rw [←ofReal_rat, ofReal_le]; exact le_of_lt h₆
        · rw [←ofReal_rat, ofReal_le]; exact le_of_lt h₈
        · simp; rw [←Rat.cast_le (K := ℝ), Rat.cast_zero]
          apply le_trans' (le_of_lt h₇)
          exact div_nonneg (le_of_lt h') (le_trans zero_le_one (le_of_lt h₄))
        · rw [←ofReal_zero, ofReal_le]; exact le_of_lt h
    · simp at h₃
      trans 0
      · simp; exact h₃
      · apply mul_nonneg <;> rw [←ofReal_zero, ofReal_le] <;> apply le_of_lt <;> assumption
  · intro a h₁; simp [upperBounds] at h₁
    apply le_of_forall_rat_lt_imp_le
    intro q h₂
    by_cases h₃ : q > 0
    · rcases exists_sqrt (@ofReal 𝓜 x * @ofReal 𝓜 y / q : 𝓜)
        (by
          apply div_nonneg
          · apply mul_nonneg <;> rw [←ofReal_zero, ofReal_le] <;> apply le_of_lt <;> assumption
          · simp; exact le_of_lt h₃) with ⟨δ, h₄, h₅⟩
      have h₆ : 1 < δ := by
        rw [←pow_lt_pow_iff_left₀ (n := 2) (by simp) h₄ (by simp)]
        rw [h₅, lt_div_iff₀]
        · simp; exact h₂
        · simp; exact h₃
      rcases exists_rat_btwn (div_lt_self (a := ofReal x) (by rw [←ofReal_zero, ofReal_lt]; exact h) h₆) with ⟨r₁, h₇, h₈⟩
      rcases exists_rat_btwn (div_lt_self (a := ofReal y) (by rw [←ofReal_zero, ofReal_lt]; exact h') h₆) with ⟨r₂, h₉, h₁₀⟩
      trans r₁ * r₂
      · have := mul_lt_mul'' h₇ h₉
          (div_nonneg (by rw [←ofReal_zero, ofReal_le]; exact le_of_lt h) (le_trans zero_le_one (le_of_lt h₆)))
          (div_nonneg (by rw [←ofReal_zero, ofReal_le]; exact le_of_lt h') (le_trans zero_le_one (le_of_lt h₆)))
        rw [←mul_div_mul_comm, ←pow_two, h₅, div_div_cancel₀] at this
        · exact le_of_lt this
        · apply ne_of_gt; apply mul_pos <;> rw [←ofReal_zero, ofReal_lt] <;> assumption
      · rw [←Rat.cast_mul]; apply h₁; simp
        apply mul_le_mul
        · rw [←ofReal_rat, ofReal_lt] at h₈; exact le_of_lt h₈
        · rw [←ofReal_rat, ofReal_lt] at h₁₀; exact le_of_lt h₁₀
        · simp; rw [←Rat.cast_le (K := 𝓜), Rat.cast_zero]
          apply le_trans' (le_of_lt h₉)
          apply div_nonneg
          · rw [←ofReal_zero, ofReal_le]; exact le_of_lt h'
          · exact (le_trans zero_le_one (le_of_lt h₆))
        · exact le_of_lt h
    · simp at h₃
      trans 0
      · simp; exact h₃
      · rw [←Rat.cast_zero]; apply h₁; simp; exact mul_nonneg (le_of_lt h) (le_of_lt h')

theorem ofReal_inv : @ofReal 𝓜 x⁻¹ = (ofReal x)⁻¹ := by
  by_cases h : x = 0
  · simp [h, ofReal_zero]
  · rw [←mul_eq_one_iff_eq_inv₀, ←ofReal_mul, inv_mul_cancel₀ h, ofReal_one]
    intro h'; rw [←ofReal_zero] at h'; exact h (ofReal_injective h')

noncomputable def model_iso_𝓡 (𝓜 : Real.Model) : 𝓡 ≃ᴹ 𝓜.toStructure where
  toEquiv := Equiv.ofBijective ofReal ⟨ofReal_injective, ofReal_surjective⟩
  on_func
  | .zero, v => by simp; apply ofReal_zero
  | .one, v => by simp; apply ofReal_one
  | .add, v => by rw [Vec.eq_two (_ ∘ _)]; apply ofReal_add
  | .neg, v => by rw [Vec.eq_one (_ ∘ _)]; apply ofReal_neg
  | .mul, v => by rw [Vec.eq_two (_ ∘ _)]; apply ofReal_mul
  on_rel
  | .le, v => by rw [Vec.eq_two (_ ∘ _)]; symm; apply ofReal_le

noncomputable def categorical : Real.Categorical
| 𝓜₁, 𝓜₂ => .trans (.symm (model_iso_𝓡 𝓜₁)) (model_iso_𝓡 𝓜₂)

end SecondOrder.Language.Theory.Real
