import MathematicalLogic.FirstOrder.Proof

namespace FirstOrder.Language

inductive Peano.Func : ℕ → Type where
| zero : Func 0
| succ : Func 1
| add : Func 2
| mul : Func 2

def Peano : Language where
  Func := Peano.Func
  Rel _ := Empty

namespace Peano

def succ (t : Peano.Term n) : Peano.Term n := .succ ⬝ᶠ [t]ᵥ
scoped notation "S" => succ

instance : Add (Peano.Term n) := ⟨(.add ⬝ᶠ [·, ·]ᵥ)⟩
instance : Mul (Peano.Term n) := ⟨(.mul ⬝ᶠ [·, ·]ᵥ)⟩

def ofNat : ℕ → Peano.Term n
| 0 => .zero ⬝ᶠ []ᵥ
| n + 1 => S (ofNat n)
instance : OfNat (Peano.Term m) n := ⟨ofNat n⟩
instance : Coe ℕ (Peano.Term m) := ⟨ofNat⟩

@[simp] theorem zero_eq : Func.zero ⬝ᶠ []ᵥ = (0 : Peano.Term n) := rfl
@[simp] theorem succ_eq : Func.succ ⬝ᶠ [t₁]ᵥ = S t₁ := rfl
@[simp] theorem add_eq {t₁ t₂ : Peano.Term n} : Func.add ⬝ᶠ [t₁, t₂]ᵥ = t₁ + t₂ := rfl
@[simp] theorem mul_eq {t₁ t₂ : Peano.Term n} : Func.mul ⬝ᶠ [t₁, t₂]ᵥ = t₁ * t₂ := rfl

@[simp] theorem subst_succ :
  (S t)[σ]ₜ = S (t[σ]ₜ) := by simp [←succ_eq, Vec.eq_one]
@[simp] theorem subst_ofNat :
  (ofNat n)[σ]ₜ = ofNat n := by
  induction n with simp [ofNat]
  | zero => simp [←zero_eq, Vec.eq_nil]
  | succ n ih => simp [ih]
@[simp] theorem subst_zero {σ : Peano.Subst n m} : 0[σ]ₜ = 0 := subst_ofNat
@[simp] theorem subst_add {t₁ t₂ : Peano.Term n} :
  (t₁ + t₂)[σ]ₜ = t₁[σ]ₜ + t₂[σ]ₜ := by simp [←add_eq, Vec.eq_two]
@[simp] theorem subst_mul {t₁ t₂ : Peano.Term n} :
  (t₁ * t₂)[σ]ₜ = t₁[σ]ₜ * t₂[σ]ₜ := by simp [←mul_eq, Vec.eq_two]
@[simp] theorem shift_ofNat : ↑ₜ(ofNat n : Peano.Term m) = ofNat n := subst_ofNat
@[simp] theorem shift_zero : ↑ₜ(0 : Peano.Term n) = 0 := subst_zero
@[simp] theorem shift_succ : ↑ₜ(S t) = S ↑ₜt := subst_succ
@[simp] theorem shift_add {t₁ t₂ : Peano.Term n} : ↑ₜ(t₁ + t₂) = ↑ₜt₁ + ↑ₜt₂ := subst_add
@[simp] theorem shift_mul {t₁ t₂ : Peano.Term n} : ↑ₜ(t₁ * t₂) = ↑ₜt₁ * ↑ₜt₂ := subst_mul

def le (t₁ t₂ : Peano.Term n) := ∃' (↑ₜt₁ + #0 ≐ ↑ₜt₂)
scoped infix:60 " ⪁ " => le
@[simp] theorem subst_le : (t₁ ⪁ t₂)[σ]ₚ = t₁[σ]ₜ ⪁ t₂[σ]ₜ := by simp [le, Term.shift_subst_lift]
@[simp] theorem shift_le : ↑ₚ(t₁ ⪁ t₂) = ↑ₜt₁ ⪁ ↑ₜt₂ := subst_le

def lt (t₁ t₂ : Peano.Term n) := S t₁ ⪁ t₂
scoped infix:60 " ⋖ " => lt
@[simp] theorem subst_lt : (t₁ ⋖ t₂)[σ]ₚ = t₁[σ]ₜ ⋖ t₂[σ]ₜ := by simp [lt]
@[simp] theorem shift_lt : ↑ₚ(t₁ ⋖ t₂) = ↑ₜt₁ ⋖ ↑ₜt₂ := subst_lt

open Lean.Parser Std in
def reprTerm : Peano.Term n → ℕ → Format
| #x, _ => "#" ++ repr x
| .zero ⬝ᶠ _, _ => "0"
| .succ ⬝ᶠ v, p => Repr.addAppParen ("S" ++ reprTerm (v 0) argPrec) p
| .add ⬝ᶠ v, p => (if p ≥ 65 then Format.paren else id) (reprTerm (v 0) 65 ++ " + " ++ reprTerm (v 1) 65)
| .mul ⬝ᶠ v, p => (if p ≥ 70 then Format.paren else id) (reprTerm (v 0) 70 ++ " * " ++ reprTerm (v 1) 70)

instance : Repr (Peano.Term n) := ⟨reprTerm⟩

open Lean.Parser Std in
def reprFormula : Peano.Formula n → ℕ → Format
| t₁ ≐ t₂, prec => (if prec ≥ 25 then Format.paren else id) (reprTerm t₁ 25 ++ " = " ++ reprTerm t₂ 25)
| (∀' (p ⇒ ⊥)) ⇒ ⊥, prec => Repr.addAppParen ("∃ " ++ reprFormula p argPrec) prec
| (p ⇒ q ⇒ ⊥) ⇒ ⊥, prec => (if prec ≥ 57 then Format.paren else id) (reprFormula p 57 ++ " ⩑ " ++ reprFormula q 57)
| (p ⇒ q) ⇒ ⊥, prec => (if prec ≥ 56 then Format.paren else id) (reprFormula p 56 ++ " ⩒ " ++ reprFormula q 56)
| ⊥ ⇒ ⊥, _ => "⊤"
| p ⇒ ⊥, prec => (if prec ≥ 58 then Format.paren else id) ("~ " ++ reprFormula p 58)
| ⊥, _ => "⊥"
| p ⇒ q, prec => (if prec ≥ 55 then Format.paren else id) (reprFormula p 55 ++ " ⇒ " ++ reprFormula q 55)
| ∀' p, prec => Repr.addAppParen ("∀ " ++ reprFormula p argPrec) prec

instance : Repr (Peano.Formula n) := ⟨reprFormula⟩
end Peano

open Peano

namespace Proof

variable {t₁ t₂ t₁' t₂' : Peano.Term n}

@[prw] theorem RwTerm.succ (h : RwTerm Γ t₁ t₂) : RwTerm Γ (S t₁) (S t₂) :=
  .func (.cons h .refl)

@[prw] theorem RwTerm.add (h₁ : RwTerm Γ t₁ t₁') (h₂ : RwTerm Γ t₂ t₂') : RwTerm Γ (t₁ + t₂) (t₁' + t₂') :=
  .func (.cons h₁ (.cons h₂ .refl))

@[prw] theorem RwTerm.mul (h₁ : RwTerm Γ t₁ t₁') (h₂ : RwTerm Γ t₂ t₂') : RwTerm Γ (t₁ * t₂) (t₁' * t₂') :=
  .func (.cons h₁ (.cons h₂ .refl))

@[prw] theorem RwFormula.le (h₁ : RwTerm Γ t₁ t₁') (h₂ : RwTerm Γ t₂ t₂') : RwFormula Γ (t₁ ⪁ t₂) (t₁' ⪁ t₂') := by
  simp [Peano.le]
  refine neg ?_
  papply iff_congr_forall
  pintro
  refine neg (eq (.add ?_ .refl) ?_)
  · exact Proof.shift h₁
  · exact Proof.shift h₂

@[prw] theorem RwFormula.lt (h₁ : RwTerm Γ t₁ t₁') (h₂ : RwTerm Γ t₂ t₂') : RwFormula Γ (t₁ ⋖ t₂) (t₁' ⋖ t₂') :=
  le (.succ h₁) h₂

end Proof

open Peano

namespace Theory

inductive PA : Peano.Theory where
| ax_succ_ne_zero : PA (∀' (~ S #0 ≐ 0))
| ax_succ_inj : PA (∀' ∀' ((S #0 ≐ S #1) ⇒ #0 ≐ #1))
| ax_add_zero : PA (∀' (#0 + 0 ≐ #0))
| ax_add_succ : PA (∀' ∀' (#0 + S #1 ≐ S (#0 + #1)))
| ax_mul_zero : PA (∀' (#0 * 0 ≐ 0))
| ax_mul_succ : PA (∀' ∀' (#0 * S #1 ≐ #0 * #1 + #0))
| ax_ind {p : Peano.Formula (n + 1)} :
  PA (∀* (p[↦ₛ 0]ₚ ⇒ (∀' (p ⇒ p[≔ₛ S #0]ₚ)) ⇒ ∀' p))

namespace PA

open Proof
attribute [local simp] Term.shift_subst_single Term.shift_subst_assign

theorem succ_ne_zero :
  ↑ᵀ^[n] PA ⊢ ~ S t ≐ 0 := by
  have h := hyp ax_succ_ne_zero
  apply Theory.foralls_elim [t]ᵥ at h
  simp at h; exact h

theorem succ_inj :
  ↑ᵀ^[n] PA ⊢ S t₁ ≐ S t₂ ⇒ t₁ ≐ t₂ := by
  have h := hyp ax_succ_inj
  apply Theory.foralls_elim [t₁, t₂]ᵥ at h
  simp at h; exact h

theorem add_zero (t) :
  ↑ᵀ^[n] PA ⊢ t + 0 ≐ t := by
  have h := hyp ax_add_zero
  apply Theory.foralls_elim [t]ᵥ at h
  simp at h; exact h

theorem add_succ (t₁ t₂) :
  ↑ᵀ^[n] PA ⊢ t₁ + S t₂ ≐ S (t₁ + t₂) := by
  have h := hyp ax_add_succ
  apply Theory.foralls_elim [t₁, t₂]ᵥ at h
  simp at h; exact h

theorem mul_zero (t) :
  ↑ᵀ^[n] PA ⊢ t * 0 ≐ 0 := by
  have h := hyp ax_mul_zero
  apply Theory.foralls_elim [t]ᵥ at h
  simp at h; exact h

theorem mul_succ (t₁ t₂) :
  ↑ᵀ^[n] PA ⊢ t₁ * S t₂ ≐ t₁ * t₂ + t₁ := by
  have h := hyp ax_mul_succ
  apply Theory.foralls_elim [t₁, t₂]ᵥ at h
  simp [Term.shift_subst_single] at h; exact h

theorem ind :
  ↑ᵀ^[n] PA ⊢ p[↦ₛ 0]ₚ ⇒ (∀' (p ⇒ p[≔ₛ S #0]ₚ)) ⇒ ∀' p := by
  have h := hyp (ax_ind (p := p))
  apply Theory.foralls_elim .id at h
  simp [Formula.subst_id] at h
  exact h

theorem add_ofNat {a b : ℕ} : ↑ᵀ^[n] PA ⊢ a + b ≐ (a + b : ℕ) := by
  induction b with
  | zero => apply add_zero
  | succ b ih => prw [add_succ, ih]; prefl

theorem mul_ofNat {a b : ℕ} : ↑ᵀ^[n] PA ⊢ a * b ≐ (a * b : ℕ) := by
  induction b with
  | zero => apply mul_zero
  | succ b ih => prw [mul_succ, ih, add_ofNat]; prefl

lemma zero_add (t) : ↑ᵀ^[n] PA ⊢ 0 + t ≐ t := by
  suffices h : PA ⊢ ∀' (0 + #0 ≐ #0) by
    apply Theory.foralls_elim [t]ᵥ at h
    simp at h; exact h
  papply ind <;> simp
  · apply add_zero
  · pintros; prw [add_succ, 0]; prefl

lemma succ_add (t₁ t₂) : ↑ᵀ^[n] PA ⊢ S t₁ + t₂ ≐ S (t₁ + t₂) := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' (S ↑ₜt₁ + #0 ≐ S (↑ₜt₁ + #0)) by
    apply (forall_elim t₂).mp at h
    simp at h; exact h
  papply ind <;> simp
  · prw [add_zero]; prefl
  · pintros; prw [add_succ, 0]; prefl

theorem add_comm (t₁ t₂) : ↑ᵀ^[n] PA ⊢ t₁ + t₂ ≐ t₂ + t₁ := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' (↑ₜt₁ + #0 ≐ #0 + ↑ₜt₁) by
    apply (forall_elim t₂).mp at h
    simp at h; exact h
  papply ind <;> simp
  · prw [zero_add, add_zero]; prefl
  · pintros; prw [add_succ, 0, succ_add]; prefl

theorem add_assoc (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ + (t₂ + t₃) ≐ t₁ + t₂ + t₃ := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' (↑ₜt₁ + (↑ₜt₂ + #0) ≐ ↑ₜt₁ + ↑ₜt₂ + #0) by
    apply (forall_elim t₃).mp at h
    simp at h; exact h
  papply ind <;> simp
  · prw [add_zero]; prefl
  · pintros; prw [add_succ, add_succ, 0]; prefl

theorem add_right_comm (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ + t₂ + t₃ ≐ t₁ + t₃ + t₂ := by
  prw [←add_assoc t₁ t₂ t₃, add_comm t₂ t₃, add_assoc]
  prefl

theorem add_right_cancel : ↑ᵀ^[n] PA ⊢ t₁ + t ≐ t₂ + t ⇒ t₁ ≐ t₂ := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' (↑ₜt₁ + #0 ≐ ↑ₜt₂ + #0 ⇒ ↑ₜt₁ ≐ ↑ₜt₂) by
    apply (forall_elim t).mp at h
    simp at h; exact h
  papply ind <;> simp
  · prw [add_zero]; pexact identity
  · pintro
    prw [add_succ]
    pintros
    papplya 1
    papply succ_inj
    passumption

theorem add_left_cancel : ↑ᵀ^[n] PA ⊢ t + t₁ ≐ t + t₂ ⇒ t₁ ≐ t₂ := by
  prw [add_comm]; exact add_right_cancel

theorem zero_mul (t) : ↑ᵀ^[n] PA ⊢ 0 * t ≐ 0 := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' (0 * #0 ≐ 0) by
    apply (forall_elim t).mp at h
    simp at h; exact h
  papply ind <;> simp
  · apply mul_zero
  · pintros; prw [mul_succ, 0, add_zero]; prefl

theorem succ_mul (t₁ t₂) : ↑ᵀ^[n] PA ⊢ S t₁ * t₂ ≐ t₁ * t₂ + t₂ := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' (S ↑ₜt₁ * #0 ≐ ↑ₜt₁ * #0 + #0) by
    apply (forall_elim t₂).mp at h
    simp at h; exact h
  papply ind <;> simp
  · prw [mul_zero, add_zero]; prefl
  · pintros
    prw [mul_succ, 0, add_succ, add_right_comm _ ↑ₜt₁]
    prefl

theorem mul_comm : ↑ᵀ^[n] PA ⊢ t₁ * t₂ ≐ t₂ * t₁ := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' (↑ₜt₁ * #0 ≐ #0 * ↑ₜt₁) by
    apply (forall_elim t₂).mp at h
    simp at h; exact h
  papply ind <;> simp
  · prw [mul_zero, zero_mul]; prefl
  · pintros; prw [mul_succ, succ_mul, 0]; prefl

theorem right_distrib (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ (t₁ + t₂) * t₃ ≐ t₁ * t₃ + t₂ * t₃ := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' ((↑ₜt₁ + ↑ₜt₂) * #0 ≐ ↑ₜt₁ * #0 + ↑ₜt₂ * #0) by
    apply (forall_elim t₃).mp at h
    simp at h; exact h
  papply ind <;> simp
  · prw [mul_zero, add_zero]; prefl
  · pintros
    prw [mul_succ, 0, add_assoc, add_right_comm (↑ₜt₁ * #0) ↑ₜt₁]
    prefl

theorem left_distrib (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ * (t₂ + t₃) ≐ t₁ * t₂ + t₁ * t₃ := by
  prw [mul_comm, right_distrib]; prefl

theorem mul_assoc (t₁ t₂ t₃) : ↑ᵀ^[n] PA ⊢ t₁ * (t₂ * t₃) ≐ t₁ * t₂ * t₃ := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' (↑ₜt₁ * (↑ₜt₂ * #0) ≐ ↑ₜt₁ * ↑ₜt₂ * #0) by
    apply (forall_elim t₃).mp at h
    simp at h; exact h
  papply ind <;> simp
  · prw [mul_zero, mul_zero]; prefl
  · pintros; prw [mul_succ, left_distrib, 0]; prefl

theorem zero_or_succ (t) : ↑ᵀ^[n] PA ⊢ t ≐ 0 ⩒ ∃' (↑ₜt ≐ S #0) := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' (#0 ≐ 0 ⩒ ∃' (#1 ≐ S #0)) by
    apply (forall_elim t).mp at h
    simp at h; exact h
  papply ind <;> simp
  · papply or_inl; prefl
  · pintros 2
    papply or_inr
    papply exists_intro #0; simp
    prefl

theorem eq_succ_of_ne_zero : ↑ᵀ^[n] PA ⊢ ~ t ≐ 0 ⇒ ∃' (↑ₜt ≐ S #0) := zero_or_succ _

lemma add_eq_zero_left : ↑ᵀ^[n] PA ⊢ t₁ + t₂ ≐ 0 ⇒ t₁ ≐ 0 := by
  pintro
  papply or_elim
  · pexact zero_or_succ t₂
  · pintro; prw [←add_zero t₁, ←0, 1, 0]; prefl
  · pintro
    papply exists_elim
    · passumption 0
    · pintros; simp
      papply false_elim
      papply succ_ne_zero (t := ↑ₜt₁ + #0)
      prw [←add_succ, ←0]
      passumption

lemma add_eq_zero_right : ↑ᵀ^[n] PA ⊢ t₁ + t₂ ≐ 0 ⇒ t₂ ≐ 0 := by
  prw [add_comm]; exact add_eq_zero_left

theorem le_ofNat {a b : ℕ} : a ≤ b → ↑ᵀ^[n] PA ⊢ a ⪁ b := by
  intro h
  papply exists_intro (b - a); simp
  prw [add_ofNat]
  rw [Nat.add_sub_cancel' h]
  prefl

theorem le_of_eq : ↑ᵀ^[n] PA ⊢ t₁ ≐ t₂ ⇒ t₁ ⪁ t₂ := by
  pintro
  papply exists_intro 0; simp
  prw [add_zero, 0]
  prefl

theorem le_refl : ↑ᵀ^[n] PA ⊢ t ⪁ t := by
  papply le_of_eq
  prefl

theorem le_antisymm : ↑ᵀ^[n] PA ⊢ t₁ ⪁ t₂ ⇒ t₂ ⪁ t₁ ⇒ t₁ ≐ t₂ := by
  pintros
  papply exists_elim
  · passumption 1
  · pintros; simp
    papply exists_elim
    · passumption 1
    · pintros; simp
      phave #1 ≐ 0
      · papply add_eq_zero_left (t₂ := #0)
        papply add_left_cancel (t := ↑ₜ↑ₜt₁)
        prw [add_assoc, 1, 0, add_zero]
        prefl
      prw [←add_zero ↑ₜ↑ₜt₁, ←0, 2]
      prefl

theorem le_trans : ↑ᵀ^[n] PA ⊢ t₁ ⪁ t₂ ⇒ t₂ ⪁ t₃ ⇒ t₁ ⪁ t₃ := by
  pintros 2
  papply exists_elim
  · passumption 1
  · pintros 2; simp
    papply exists_elim
    · passumption 1
    · pintros 2; simp
      papply exists_intro (#1 + #0); simp
      prw [add_assoc, 1, 0]
      prefl

theorem zero_le : ↑ᵀ^[n] PA ⊢ 0 ⪁ t := by
  papply exists_intro t; simp
  apply zero_add

theorem le_zero_iff : ↑ᵀ^[n] PA ⊢ t ⪁ 0 ⇔ t ≐ 0 := by
  papply iff_intro
  · pintro
    papply exists_elim
    · passumption 0
    · pintros; simp
      papply add_eq_zero_left
      passumption 0
  · pintro
    papply exists_intro 0; simp
    prw [0, add_zero]
    prefl

theorem le_succ_self : ↑ᵀ^[n] PA ⊢ t ⪁ S t := by
  papply exists_intro 1; simp
  prw [add_succ, add_zero]
  prefl

theorem le_succ_iff : ↑ᵀ^[n] PA ⊢ t₁ ⪁ S t₂ ⇔ t₁ ⪁ t₂ ⩒ t₁ ≐ S t₂ := by
  papply iff_intro
  · pintro
    papply exists_elim
    · passumption 0
    · pintros 2; simp
      papply or_elim
      · pexact zero_or_succ #0
      · pintro
        papply or_inr
        prw [←1, 0, add_zero]
        prefl
      · pintro
        papply exists_elim
        · passumption 0
        · pintros 2; simp
          papply or_inl
          papply exists_intro #0; simp
          papply succ_inj
          prw [←2, 0, add_succ]
          prefl
  · pintro
    papply or_elim
    · passumption 0
    · pintro
      papply le_trans
      · passumption 0
      · pexact le_succ_self
    · pintro
      papply le_of_eq
      passumption

theorem succ_le_succ_iff : ↑ᵀ^[n] PA ⊢ S t₁ ⪁ S t₂ ⇔ t₁ ⪁ t₂ := by
  papply iff_intro
  · pintro
    papply exists_elim
    · passumption 0
    · pintros 2; simp
      papply exists_intro #0; simp
      papply succ_inj
      prw [←0, succ_add]
      prefl
  · pintro
    papply exists_elim
    · passumption 0
    · pintros 2; simp
      papply exists_intro #0; simp
      prw [←0, succ_add]
      prefl

theorem add_le_add : ↑ᵀ^[n] PA ⊢ t₁ ⪁ t₂ ⇒ t₃ ⪁ t₄ ⇒ t₁ + t₃ ⪁ t₂ + t₄ := by
  pintros 2
  papply exists_elim
  · passumption 1
  · pintros 2; simp
    papply exists_elim
    · passumption 1
    · pintros 2; simp
      papply exists_intro (#0 + #1); simp
      prw [add_assoc, ←add_assoc _ _ #0, 0, add_right_comm, 1]
      prefl

theorem add_le_add_left : ↑ᵀ^[n] PA ⊢ t₁ ⪁ t₂ ⇒ t + t₁ ⪁ t + t₂ := by
  pintro
  papply add_le_add
  · pexact le_refl
  · passumption

theorem add_le_add_right : ↑ᵀ^[n] PA ⊢ t₁ ⪁ t₂ ⇒ t₁ + t ⪁ t₂ + t := by
  pintro
  papply add_le_add
  · passumption
  · pexact le_refl

theorem lt_ofNat {a b : ℕ} : a < b → ↑ᵀ^[n] PA ⊢ a ⋖ b := by
  intro h
  rw [←Nat.succ_le_iff] at h
  exact le_ofNat h

theorem le_of_lt : ↑ᵀ^[n] PA ⊢ t₁ ⋖ t₂ ⇒ t₁ ⪁ t₂ := by
  pintro
  papply exists_elim
  · passumption 0
  · pintros 2; simp
    papply exists_intro (S #0); simp [Term.shift_subst_single]
    prw [←0, add_succ, succ_add]
    prefl

theorem ne_of_lt : ↑ᵀ^[n] PA ⊢ t₁ ⋖ t₂ ⇒ ~ t₁ ≐ t₂ := by
  pintros
  papply exists_elim
  · passumption 1
  · pintros; simp
    papply succ_ne_zero (t := #0)
    papply add_left_cancel (t := ↑ₜt₂)
    prw [add_zero, ←1, add_succ, ←succ_add, 0, 1]
    prefl

theorem le_iff_lt_or_eq : ↑ᵀ^[n] PA ⊢ t₁ ⪁ t₂ ⇔ t₁ ⋖ t₂ ⩒ t₁ ≐ t₂ := by
  papply iff_intro
  · pintro
    papply exists_elim
    · passumption 0
    · pintros 2; simp
      papply or_elim
      · pexact zero_or_succ #0
      · pintro
        papply or_inr
        prw [←1, 0, add_zero]
        prefl
      · pintro
        papply or_inl
        papply exists_elim
        · passumption 0
        pintros 2; simp
        papply exists_intro #0; simp [Term.shift_subst_single]
        prw [succ_add, ←add_succ, ←0, 2]
        prefl
  · pintro
    papply or_elim
    · passumption 0
    · pintro
      papply le_of_lt
      passumption
    · pintro
      papply le_of_eq
      passumption

theorem lt_or_eq_of_le : ↑ᵀ^[n] PA ⊢ t₁ ⪁ t₂ ⇒ t₁ ⋖ t₂ ⩒ t₁ ≐ t₂ := by
  papply iff_mp
  pexact le_iff_lt_or_eq

theorem lt_succ_iff : ↑ᵀ^[n] PA ⊢ t₁ ⋖ S t₂ ⇔ t₁ ⪁ t₂ := succ_le_succ_iff

theorem succ_lt_succ_iff : ↑ᵀ^[n] PA ⊢ S t₁ ⋖ S t₂ ⇔ t₁ ⋖ t₂ := succ_le_succ_iff

theorem lt_of_le_of_lt : ↑ᵀ^[n] PA ⊢ t₁ ⪁ t₂ ⇒ t₂ ⋖ t₃ ⇒ t₁ ⋖ t₃ := by
  pintros 2
  papply le_trans (t₂ := S t₂)
  · prw [succ_le_succ_iff]
    passumption 1
  · passumption 0

theorem not_lt_zero : ↑ᵀ^[n] PA ⊢ ~ t ⋖ 0 := by
  pintro
  papply exists_elim
  · passumption 0
  · simp; pintro; prw [succ_add]; pexact succ_ne_zero

theorem lt_succ_self : ↑ᵀ^[n] PA ⊢ t ⋖ S t := by
  prw [lt_succ_iff]; pexact le_refl

theorem le_or_gt : ↑ᵀ^[n] PA ⊢ t₁ ⪁ t₂ ⩒ t₂ ⋖ t₁ := by
  suffices h : ↑ᵀ^[n] PA ⊢ ∀' (#0 ⪁ ↑ₜt₂ ⩒ ↑ₜt₂ ⋖ #0) by
    apply (forall_elim t₁).mp at h
    simp at h; exact h
  papply ind <;> simp
  · papply or_inl
    pexact zero_le
  · pintros 2
    papply or_elim
    · passumption 0
    · pintro
      papply or_elim
      · papply lt_or_eq_of_le with 1
        passumption 0
      · pintro
        papply or_inl
        prw [←lt_succ_iff]
        papply lt_of_le_of_lt
        · passumption 0
        · pexact lt_succ_self
      · pintro
        papply or_inr
        prw [0]
        pexact lt_succ_self
    · pintro
      papply or_inr
      papply lt_of_le_of_lt
      · papply le_of_lt
        passumption 0
      · pexact lt_succ_self

theorem ne_ofNat {a b : ℕ} : a ≠ b → ↑ᵀ^[n] PA ⊢ ~ a ≐ b := by
  intro h
  rcases lt_or_gt_of_ne h with h | h
  · papply ne_of_lt
    pexact lt_ofNat h
  · papply ne_symm
    papply ne_of_lt
    pexact lt_ofNat h

end FirstOrder.Language.Theory.PA
