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

def succ (t : Peano.Term n) : Peano.Term n := .succ ⬝ₜ [t]ᵥ
scoped notation "S" => succ

instance : Add (Peano.Term n) := ⟨(.add ⬝ₜ [·, ·]ᵥ)⟩
instance : Mul (Peano.Term n) := ⟨(.mul ⬝ₜ [·, ·]ᵥ)⟩

def ofNat : ℕ → Peano.Term n
| 0 => .zero ⬝ₜ []ᵥ
| n + 1 => S (ofNat n)
instance : OfNat (Peano.Term m) n := ⟨ofNat n⟩
instance : Coe ℕ (Peano.Term m) := ⟨ofNat⟩

@[simp] theorem zero_eq : Func.zero ⬝ₜ []ᵥ = (0 : Peano.Term n) := rfl
@[simp] theorem succ_eq : Func.succ ⬝ₜ [t₁]ᵥ = S t₁ := rfl
@[simp] theorem add_eq {t₁ t₂ : Peano.Term n} : Func.add ⬝ₜ [t₁, t₂]ᵥ = t₁ + t₂ := rfl
@[simp] theorem mul_eq {t₁ t₂ : Peano.Term n} : Func.mul ⬝ₜ [t₁, t₂]ᵥ = t₁ * t₂ := rfl

scoped notation "⌜" x "⌝" => ofNat (Encodable.encode x)
@[simp] theorem ofNat_eq [Encodable α] {a : α} : (⌜a⌝ : Peano.Term n) = Encodable.encode a := rfl

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

@[simp] theorem Term.subst_le : (t₁ ⪁ t₂)[σ]ₚ = t₁[σ]ₜ ⪁ t₂[σ]ₜ := by
  simp [le, Term.shift_subst_lift]
@[simp] theorem Term.shift_le : ↑ₚ(t₁ ⪁ t₂) = ↑ₜt₁ ⪁ ↑ₜt₂ := Term.subst_le

instance : Encodable (Language.Func Peano n) where
  encode
  | .zero => 0
  | .succ => 0
  | .add => 0
  | .mul => 1
  decode m :=
    match n, m with
    | 0, 0 => some .zero
    | 1, 0 => some .succ
    | 2, 0 => some .add
    | 2, 1 => some .mul
    | _, _ => none
  encodek f := by cases f <;> rfl

instance : Encodable (Peano.Rel n) := IsEmpty.toEncodable (α := Empty)

open Lean.Parser Std in
def reprTerm : Peano.Term n → ℕ → Format
| #x, _ => "#" ++ repr x
| .zero ⬝ₜ _, _ => "0"
| .succ ⬝ₜ v, p => Repr.addAppParen ("S" ++ reprTerm (v 0) argPrec) p
| .add ⬝ₜ v, p => (if p ≥ 65 then Format.paren else id) (reprTerm (v 0) 65 ++ " + " ++ reprTerm (v 1) 65)
| .mul ⬝ₜ v, p => (if p ≥ 70 then Format.paren else id) (reprTerm (v 0) 70 ++ " * " ++ reprTerm (v 1) 70)

instance : Repr (Peano.Term n) := ⟨reprTerm⟩

open Lean.Parser Std in
def reprFormula : Peano.Formula n → ℕ → Format
| t₁ ≐ t₂, prec => (if prec ≥ 25 then Format.paren else id) (reprTerm t₁ 25 ++ " = " ++ reprTerm t₂ 25)
| ⊥, _ => "⊥"
| p ⇒ q, prec => (if prec ≥ 55 then Format.paren else id) (reprFormula p 55 ++ " ⇒ " ++ reprFormula q 55)
| ∀' p, prec => Repr.addAppParen ("∀ " ++ reprFormula p argPrec) prec

instance : Repr (Peano.Formula n) := ⟨reprFormula⟩

end Peano

namespace Theory

open Peano

inductive PA : Peano.Theory where
| ax_succ_ne_zero : PA (∀' (~ S #0 ≐ 0))
| ax_succ_inj : PA (∀' ∀' ((S #0 ≐ S #1) ⇒ #0 ≐ #1))
| ax_add_zero : PA (∀' #0 + 0 ≐ #0)
| ax_add_succ : PA (∀' ∀' #0 + S #1 ≐ S (#0 + #1))
| ax_mul_zero : PA (∀' #0 * 0 ≐ 0)
| ax_mul_succ : PA (∀' ∀' #0 * S #1 ≐ #0 * #1 + #0)
| ax_ind {p : Peano.Formula (n + 1)} :
  PA (∀* (p[↦ₛ 0]ₚ ⇒ (∀' (p ⇒ p[≔ₛ (S #0)]ₚ)) ⇒ ∀' p))

namespace PA

theorem succ_ne_zero :
  ↑ᴳ^[k] PA ⊢ ~ S t ≐ 0 := by
  have h := Proof.hyp ax_succ_ne_zero
  apply Theory.foralls_elim (σ := [t]ᵥ) at h
  simp at h; exact h

theorem succ_inj :
  ↑ᴳ^[k] PA ⊢ S t₁ ≐ S t₂ ⇒ t₁ ≐ t₂ := by
  have h := Proof.hyp ax_succ_inj
  apply Theory.foralls_elim (σ := [t₁, t₂]ᵥ) at h
  simp [Term.shift_subst_single] at h; exact h

theorem add_zero (t) :
  ↑ᴳ^[k] PA ⊢ t + 0 ≐ t := by
  have h := Proof.hyp ax_add_zero
  apply Theory.foralls_elim (σ := [t]ᵥ) at h
  simp at h; exact h

theorem add_succ (t₁ t₂) :
  ↑ᴳ^[k] PA ⊢ t₁ + S t₂ ≐ S (t₁ + t₂) := by
  have h := Proof.hyp ax_add_succ
  apply Theory.foralls_elim (σ := [t₁, t₂]ᵥ) at h
  simp [Term.shift_subst_single] at h; exact h

theorem mul_zero (t) :
  ↑ᴳ^[k] PA ⊢ t * 0 ≐ 0 := by
  have h := Proof.hyp ax_mul_zero
  apply Theory.foralls_elim (σ := [t]ᵥ) at h
  simp at h; exact h

theorem mul_succ (t₁ t₂) :
  ↑ᴳ^[k] PA ⊢ t₁ * S t₂ ≐ t₁ * t₂ + t₁ := by
  have h := Proof.hyp ax_mul_succ
  apply Theory.foralls_elim (σ := [t₁, t₂]ᵥ) at h
  simp [Term.shift_subst_single] at h; exact h

theorem ind :
  ↑ᴳ^[k] PA ⊢ p[↦ₛ 0]ₚ ⇒ (∀' (p ⇒ p[≔ₛ (S #0)]ₚ)) ⇒ ∀' p := by
  have h := Proof.hyp (ax_ind (p := p))
  apply Theory.foralls_elim (σ := .id) at h
  simp [Formula.subst_id] at h
  exact h

theorem add_ofNat {n m : ℕ} : ↑ᴳ^[k] PA ⊢ n + m ≐ (n + m: ℕ) := by
  induction m with
  | zero => apply add_zero
  | succ m ih => prw [add_succ, ih]; prefl

theorem mul_ofNat {n m : ℕ} : ↑ᴳ^[k] PA ⊢ n * m ≐ (n * m : ℕ) := by
  induction m with
  | zero => apply mul_zero
  | succ m ih => prw [mul_succ, ih, add_ofNat]; prefl

lemma zero_add (t) : ↑ᴳ^[k] PA ⊢ 0 + t ≐ t := by
  suffices h : PA ⊢ ∀' (0 + #0 ≐ #0) by
    apply Theory.foralls_elim (σ := [t]ᵥ) at h
    simp at h; exact h
  papply ind <;> simp
  · apply add_zero
  · pintros; prw [add_succ, 0]; prefl

lemma succ_add (t₁ t₂) : ↑ᴳ^[k] PA ⊢ S t₁ + t₂ ≐ S (t₁ + t₂) := by
  suffices h : ↑ᴳ^[k] PA ⊢ ∀' (S ↑ₜt₁ + #0 ≐ S (↑ₜt₁ + #0)) by
    apply Proof.mp (Proof.forall_elim (t := t₂)) at h
    simp [Term.shift_subst_single] at h; exact h
  papply ind <;> simp [Term.shift_subst_single, Term.shift_subst_assign]
  · prw [add_zero]; prefl
  · pintros; prw [add_succ, 0]; prefl

theorem add_comm (t₁ t₂) : ↑ᴳ^[k] PA ⊢ t₁ + t₂ ≐ t₂ + t₁ := by
  suffices h : ↑ᴳ^[k] PA ⊢ ∀' (↑ₜt₁ + #0 ≐ #0 + ↑ₜt₁) by
    apply Proof.mp (Proof.forall_elim (t := t₂)) at h
    simp [Term.shift_subst_single] at h; exact h
  papply ind <;> simp [Term.shift_subst_single, Term.shift_subst_assign]
  · prw [zero_add, add_zero]; prefl
  · pintros; prw [add_succ, 0, succ_add]; prefl

theorem add_assoc (t₁ t₂ t₃) : ↑ᴳ^[k] PA ⊢ t₁ + (t₂ + t₃) ≐ t₁ + t₂ + t₃ := by
  suffices h : ↑ᴳ^[k] PA ⊢ ∀' (↑ₜt₁ + (↑ₜt₂ + #0) ≐ ↑ₜt₁ + ↑ₜt₂ + #0) by
    apply Proof.mp (Proof.forall_elim (t := t₃)) at h
    simp [Term.shift_subst_single] at h; exact h
  papply ind <;> simp [Term.shift_subst_single, Term.shift_subst_assign]
  · prw [add_zero]; prefl
  · pintros; prw [add_succ, add_succ, 0]; prefl

theorem add_right_comm (t₁ t₂ t₃) : ↑ᴳ^[k] PA ⊢ t₁ + t₂ + t₃ ≐ t₁ + t₃ + t₂ := by
  prw [←add_assoc t₁ t₂ t₃, add_comm t₂ t₃, add_assoc]
  prefl

theorem add_right_cancel : ↑ᴳ^[k] PA ⊢ t₁ + t ≐ t₂ + t ⇒ t₁ ≐ t₂ := by
  suffices h : ↑ᴳ^[k] PA ⊢ ∀' (↑ₜt₁ + #0 ≐ ↑ₜt₂ + #0 ⇒ ↑ₜt₁ ≐ ↑ₜt₂) by
    apply Proof.mp (Proof.forall_elim (t := t)) at h
    simp [Term.shift_subst_single] at h; exact h
  papply ind <;> simp [Term.shift_subst_single, Term.shift_subst_assign]
  · prw [add_zero]; pintro; passumption
  · pintro
    prw [add_succ]
    pintros
    papplya 1
    papply succ_inj
    passumption

theorem add_left_cancel : ↑ᴳ^[k] PA ⊢ t + t₁ ≐ t + t₂ ⇒ t₁ ≐ t₂ := by
  prw [add_comm]; exact add_right_cancel

theorem zero_mul (t) : ↑ᴳ^[k] PA ⊢ 0 * t ≐ 0 := by
  suffices h : ↑ᴳ^[k] PA ⊢ ∀' (0 * #0 ≐ 0) by
    apply Proof.mp (Proof.forall_elim (t := t)) at h
    simp at h; exact h
  papply ind <;> simp
  · apply mul_zero
  · pintros; prw [mul_succ, 0, add_zero]; prefl

theorem succ_mul (t₁ t₂) : ↑ᴳ^[k] PA ⊢ S t₁ * t₂ ≐ t₁ * t₂ + t₂ := by
  suffices h : ↑ᴳ^[k] PA ⊢ ∀' (S ↑ₜt₁ * #0 ≐ ↑ₜt₁ * #0 + #0) by
    apply Proof.mp (Proof.forall_elim (t := t₂)) at h
    simp [Term.shift_subst_single] at h; exact h
  papply ind <;> simp [Term.shift_subst_assign]
  · prw [mul_zero, add_zero]; prefl
  · pintros
    prw [mul_succ, 0, add_succ, add_right_comm _ ↑ₜt₁]
    prefl

theorem mul_comm : ↑ᴳ^[k] PA ⊢ t₁ * t₂ ≐ t₂ * t₁ := by
  suffices h : ↑ᴳ^[k] PA ⊢ ∀' (↑ₜt₁ * #0 ≐ #0 * ↑ₜt₁) by
    apply Proof.mp (Proof.forall_elim (t := t₂)) at h
    simp [Term.shift_subst_single] at h; exact h
  papply ind <;> simp [Term.shift_subst_assign]
  · prw [mul_zero, zero_mul]; prefl
  · pintros; prw [mul_succ, succ_mul, 0]; prefl

theorem right_distrib (t₁ t₂ t₃) : ↑ᴳ^[k] PA ⊢ (t₁ + t₂) * t₃ ≐ t₁ * t₃ + t₂ * t₃ := by
  suffices h : ↑ᴳ^[k] PA ⊢ ∀' ((↑ₜt₁ + ↑ₜt₂) * #0 ≐ ↑ₜt₁ * #0 + ↑ₜt₂ * #0) by
    apply Proof.mp (Proof.forall_elim (t := t₃)) at h
    simp [Term.shift_subst_single] at h; exact h
  papply ind <;> simp [Term.shift_subst_single, Term.shift_subst_assign]
  · prw [mul_zero, add_zero]; prefl
  · pintros
    prw [mul_succ, 0, add_assoc, add_right_comm (↑ₜt₁ * #0) ↑ₜt₁]
    prefl

theorem left_distrib (t₁ t₂ t₃) : ↑ᴳ^[k] PA ⊢ t₁ * (t₂ + t₃) ≐ t₁ * t₂ + t₁ * t₃ := by
  prw [mul_comm, right_distrib]; prefl

theorem mul_assoc (t₁ t₂ t₃) : ↑ᴳ^[k] PA ⊢ t₁ * (t₂ * t₃) ≐ t₁ * t₂ * t₃ := by
  suffices h : ↑ᴳ^[k] PA ⊢ ∀' (↑ₜt₁ * (↑ₜt₂ * #0) ≐ ↑ₜt₁ * ↑ₜt₂ * #0) by
    apply Proof.mp (Proof.forall_elim (t := t₃)) at h
    simp [Term.shift_subst_single] at h; exact h
  papply ind <;> simp [Term.shift_subst_single, Term.shift_subst_assign]
  · prw [mul_zero, mul_zero]; prefl
  · pintros; prw [mul_succ, left_distrib, 0]; prefl

theorem zero_or_succ (t) : ↑ᴳ^[k] PA ⊢ t ≐ 0 ⩒ ∃' (↑ₜt ≐ S #0) := by
  suffices h : ↑ᴳ^[k] PA ⊢ ∀' (#0 ≐ 0 ⩒ ∃' (#1 ≐ S #0)) by
    apply Proof.mp (Proof.forall_elim (t := t)) at h
    simp at h; exact h
  papply ind <;> simp
  · papply Proof.or_inl; prefl
  · pintros 2
    papply Proof.or_inr
    papply Proof.exists_intro #0
    simp
    prefl

theorem eq_succ_of_ne_zero : ↑ᴳ^[k] PA ⊢ ~ t ≐ 0 ⇒ ∃' (↑ₜt ≐ S #0) := zero_or_succ _

lemma add_eq_zero_left : ↑ᴳ^[k] PA ⊢ t₁ + t₂ ≐ 0 ⇒ t₁ ≐ 0 := by
  pintro
  papply Proof.or_elim
  · pexact zero_or_succ t₂
  · pintro; prw [←add_zero t₁, ←0, 1, 0]; prefl
  · pintro
    papply Proof.exists_elim
    · passumption 0
    · pintros; simp
      papply Proof.false_elim
      papply succ_ne_zero (t := ↑ₜt₁ + #0)
      prw [←add_succ, ←0]
      passumption

lemma add_eq_zero_right : ↑ᴳ^[k] PA ⊢ t₁ + t₂ ≐ 0 ⇒ t₂ ≐ 0 := by
  prw [add_comm]; exact add_eq_zero_left

theorem le_ofNat {n m : ℕ} : n ≤ m → ↑ᴳ^[k] PA ⊢ n ⪁ m := by
  intro h
  papply Proof.exists_intro (m - n)
  simp [Term.shift_subst_single]
  prw [add_ofNat]
  rw [Nat.add_sub_cancel' h]
  prefl

theorem le_refl : ↑ᴳ^[k] PA ⊢ t ⪁ t := by
  papply Proof.exists_intro 0
  simp [Term.shift_subst_single]
  apply add_zero

theorem le_antisymm : ↑ᴳ^[k] PA ⊢ t₁ ⪁ t₂ ⇒ t₂ ⪁ t₁ ⇒ t₁ ≐ t₂ := by
  pintros
  papply Proof.exists_elim
  · passumption 1
  · pintros; simp
    papply Proof.exists_elim
    · passumption 1
    · pintros; simp
      phave #1 ≐ 0
      · papply add_eq_zero_left (t₂ := #0)
        papply add_left_cancel (t := ↑ₜ↑ₜt₁)
        prw [add_assoc, 1, 0, add_zero]
        prefl
      prw [←add_zero ↑ₜ↑ₜt₁, ←0, 2]
      prefl

theorem le_trans : ↑ᴳ^[k] PA ⊢ t₁ ⪁ t₂ ⇒ t₂ ⪁ t₃ ⇒ t₁ ⪁ t₃ := by
  pintros 2
  papply Proof.exists_elim
  · passumption 1
  · pintros 2; simp
    papply Proof.exists_elim
    · passumption 1
    · pintros 2; simp
      papply Proof.exists_intro (#1 + #0)
      simp [Term.shift_subst_single]
      prw [add_assoc, 1, 0]
      prefl

theorem zero_le : ↑ᴳ^[k] PA ⊢ 0 ⪁ t := by
  papply Proof.exists_intro t
  simp [Term.shift_subst_single]
  apply zero_add

theorem le_succ_self : ↑ᴳ^[k] PA ⊢ t ⪁ S t := by
  papply Proof.exists_intro 1
  simp [Term.shift_subst_single]
  prw [add_succ, add_zero]
  prefl

theorem add_le_add : ↑ᴳ^[k] PA ⊢ t₁ ⪁ t₂ ⇒ t₃ ⪁ t₄ ⇒ t₁ + t₃ ⪁ t₂ + t₄ := by
  pintros 2
  papply Proof.exists_elim
  · passumption 1
  · pintros 2; simp
    papply Proof.exists_elim
    · passumption 1
    · pintros 2; simp
      papply Proof.exists_intro (#0 + #1)
      simp [Term.shift_subst_single]
      prw [add_assoc, ←add_assoc _ _ #0, 0, add_right_comm, 1]
      prefl

theorem add_le_add_left : ↑ᴳ^[k] PA ⊢ t₁ ⪁ t₂ ⇒ t + t₁ ⪁ t + t₂ := by
  pintro
  papply add_le_add
  · pexact le_refl
  · passumption

theorem add_le_add_right : ↑ᴳ^[k] PA ⊢ t₁ ⪁ t₂ ⇒ t₁ + t ⪁ t₂ + t := by
  pintro
  papply add_le_add
  · passumption
  · pexact le_refl

theorem lt_ofNat {n m : ℕ} : n < m → ↑ᴳ^[k] PA ⊢ n ⋖ m := by
  intro h
  rw [←Nat.succ_le_iff] at h
  exact le_ofNat h

theorem le_of_lt : ↑ᴳ^[k] PA ⊢ t₁ ⋖ t₂ ⇒ t₁ ⪁ t₂ := by
  pintro
  papply Proof.exists_elim
  · passumption 0
  · pintros 2; simp
    papply Proof.exists_intro (S #0); simp [Term.shift_subst_single]
    prw [←0, add_succ, succ_add]
    prefl

theorem ne_of_lt : ↑ᴳ^[k] PA ⊢ t₁ ⋖ t₂ ⇒ ~ t₁ ≐ t₂ := by
  pintros
  papply Proof.exists_elim
  · passumption 1
  · pintros; simp
    papply succ_ne_zero (t := #0)
    papply add_left_cancel (t := ↑ₜt₂)
    prw [add_zero, ←1, add_succ, ←succ_add, 0, 1]
    prefl

theorem eq_or_lt_of_le : ↑ᴳ^[k] PA ⊢ t₁ ⪁ t₂ ⇒ t₁ ≐ t₂ ⩒ t₁ ⋖ t₂ := by
  pintro
  papply Proof.exists_elim
  · passumption 0
  · pintros 2; simp
    papply Proof.or_elim
    · pexact zero_or_succ #0
    · pintro
      papply Proof.or_inl
      prw [←1, 0, add_zero]
      prefl
    · pintro
      papply Proof.or_inr
      papply Proof.exists_elim
      · passumption 0
      pintros 2; simp
      papply Proof.exists_intro #0; simp [Term.shift_subst_single]
      prw [succ_add, ←add_succ, ←0, 2]
      prefl

theorem lt_of_le_of_ne : ↑ᴳ^[k] PA ⊢ t₁ ⪁ t₂ ⇒ ~ t₁ ≐ t₂ ⇒ t₁ ⋖ t₂ := eq_or_lt_of_le

theorem ne_ofNat {n m : ℕ} : n ≠ m → ↑ᴳ^[k] PA ⊢ ~ n ≐ m := by
  intro h
  rcases lt_or_gt_of_ne h with h | h
  · papply ne_of_lt
    pexact lt_ofNat h
  · papply Proof.ne_symm
    papply ne_of_lt
    pexact lt_ofNat h

end FirstOrder.Language.Theory.PA
