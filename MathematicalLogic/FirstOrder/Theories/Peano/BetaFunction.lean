import Mathlib.Logic.Godel.GodelBetaFunction
import MathematicalLogic.FirstOrder.Theories.Peano.Hierarchy

/-!

# Gödel's beta function

This file formalizes Gödel's beta function, and proves its properties in `Q` and `PA`. Gödel's beta
function enables encoding of finite sequences, which is a crucial step towards the representation
theorem.

In `Q`, we only prove its representability (`beta_ofNat`). In `PA`, we also prove its uniqueness
(`beta_unique`), totality (`beta_total`), and the comprehension theorem (`beta_comprehension`). The
comprehension theorem allows us to encode a finite sequence described by a formula; to prove that,
we have to formalize the Chinese remainder theorem in `PA`.

## References

* A Concise Introduction to Mathematical Logic (third edition), Wolfgang Rautenberg.

-/

namespace Vec

def unbeta (v : Vec ℕ n) := Nat.unbeta (.ofFn v)

theorem beta_unbeta (v : Vec ℕ n) (i : Fin n) : Nat.beta (unbeta v) i = v i := by
  have := Nat.beta_unbeta_coe (.ofFn v) (i.cast List.length_ofFn.symm)
  simp at this; exact this

end Vec

namespace FirstOrder.Language

variable {t t' t₁ t₁' t₂ t₂' t₃ t₄ : peano.Term n}

namespace peano

open Proof

/-- Pairing function (the same as `Nat.pair`). -/
def pair (t t₁ t₂ : peano.Term n) := t₁ ≺ t₂ ⩑ t ≐ t₂ * t₂ + t₁ ⩒ t₂ ⪯ t₁ ⩑ t ≐ t₁ * t₁ + t₁ + t₂
@[simp] theorem subst_pair : (pair t t₁ t₂)[σ]ₚ = pair t[σ]ₜ t₁[σ]ₜ t₂[σ]ₜ := by simp [pair]
@[simp] theorem shift_pair : ↑ₚ(pair t t₁ t₂) = pair ↑ₜt ↑ₜt₁ ↑ₜt₂ := subst_pair
@[aesop safe] theorem Sigma₁.pair : Sigma₁ (pair t t₁ t₂) := by simp [peano.pair]; aesop
@[prw] theorem iff_congr_pair :
  Γ ⊢ t ≐ t' ⇒ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ pair t t₁ t₂ ⇔ pair t' t₁' t₂' := by
  pintros 3; simp [pair]; prw [0, 1, 2]; prefl

/-- Remainder function. -/
def mod (t t₁ t₂ : peano.Term n) := t ≺ t₂ ⩑ ∃[≺ S t₁] (#0 * ↑ₜt₂ + ↑ₜt ≐ ↑ₜt₁)
@[simp] theorem subst_mod : (mod t t₁ t₂)[σ]ₚ = mod t[σ]ₜ t₁[σ]ₜ t₂[σ]ₜ := by simp [mod, Term.shift_subst_lift]
@[simp] theorem shift_mod : ↑ₚ(mod t t₁ t₂) = mod ↑ₜt ↑ₜt₁ ↑ₜt₂ := subst_mod
@[aesop safe] theorem Sigma₁.mod : Sigma₁ (mod t t₁ t₂) := by simp [peano.mod]; aesop
@[prw] theorem iff_congr_mod :
  Γ ⊢ t ≐ t' ⇒ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ mod t t₁ t₂ ⇔ mod t' t₁' t₂' := by
  pintros 3
  simp [mod]
  papply iff_congr_and
  · prw [0, 2]; prefl
  · papply iff_congr_exists; pintro; simp; prw [0, 1, 2]; prefl

/-- The negation of remainder function, in Σ₁. -/
def nmod (t t₁ t₂ : peano.Term n) := t₂ ⪯ t ⩒ ∀[≺ S t₁] (~ #0 * ↑ₜt₂ + ↑ₜt ≐ ↑ₜt₁)
@[simp] theorem subst_nmod : (nmod t t₁ t₂)[σ]ₚ = nmod t[σ]ₜ t₁[σ]ₜ t₂[σ]ₜ := by simp [nmod, Term.shift_subst_lift]
@[simp] theorem shift_nmod : ↑ₚ(nmod t t₁ t₂) = nmod ↑ₜt ↑ₜt₁ ↑ₜt₂ := subst_nmod
@[aesop safe] theorem Sigma₁.nmod : Sigma₁ (nmod t t₁ t₂) := by simp [peano.nmod]; aesop
@[prw] theorem iff_congr_nmod :
  Γ ⊢ t ≐ t' ⇒ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ nmod t t₁ t₂ ⇔ nmod t' t₁' t₂' := by
  pintros 3
  simp [nmod]
  papply iff_congr_or
  · prw [0, 2]; prefl
  · papply iff_congr_forall; pintro; simp; prw [0, 1, 2]; prefl

/-- Gödel's beta function. -/
def beta (t t₁ t₂ : peano.Term n) := ∃[≺ S t₁] ∃[≺ S ↑ₜt₁] (pair ↑ₜ↑ₜt₁ #1 #0 ⩑ mod ↑ₜ↑ₜt #1 (S (S ↑ₜ↑ₜt₂ * #0)))
@[simp] theorem subst_beta : (beta t t₁ t₂)[σ]ₚ = beta t[σ]ₜ t₁[σ]ₜ t₂[σ]ₜ := by simp [beta, Term.shift_subst_lift]
@[simp] theorem shift_beta : ↑ₚ(beta t t₁ t₂) = beta ↑ₜt ↑ₜt₁ ↑ₜt₂ := subst_beta
@[aesop safe] theorem Sigma₁.beta : Sigma₁ (beta t t₁ t₂) := by simp [peano.beta]; aesop
@[prw] theorem iff_congr_beta :
  Γ ⊢ t ≐ t' ⇒ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ beta t t₁ t₂ ⇔ beta t' t₁' t₂' := by
  pintros 3
  simp [beta]
  papply iff_congr_exists; pintro
  papply iff_congr_and; simp
  · prw [1]; prefl
  · papply iff_congr_exists; pintro; simp
    prw [0, 1, 2]; prefl

/-- The negation of Gödel's beta function, in Σ₁. -/
def nbeta (t t₁ t₂ : peano.Term n) := ∃[≺ S t₁] ∃[≺ S ↑ₜt₁] (pair ↑ₜ↑ₜt₁ #1 #0 ⩑ nmod ↑ₜ↑ₜt #1 (S (S ↑ₜ↑ₜt₂ * #0)))
@[simp] theorem subst_nbeta : (nbeta t t₁ t₂)[σ]ₚ = nbeta t[σ]ₜ t₁[σ]ₜ t₂[σ]ₜ := by simp [nbeta, Term.shift_subst_lift]
@[simp] theorem shift_nbeta : ↑ₚ(nbeta t t₁ t₂) = nbeta ↑ₜt ↑ₜt₁ ↑ₜt₂ := subst_nbeta
@[aesop safe] theorem Sigma₁.nbeta : Sigma₁ (nbeta t t₁ t₂) := by simp [peano.nbeta]; aesop
@[prw] theorem iff_congr_nbeta :
  Γ ⊢ t ≐ t' ⇒ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ nbeta t t₁ t₂ ⇔ nbeta t' t₁' t₂' := by
  pintros 3
  simp [nbeta]
  papply iff_congr_exists; pintro
  papply iff_congr_and; simp
  · prw [1]; prefl
  · papply iff_congr_exists; pintro; simp
    prw [0, 1, 2]; prefl

def dvd (t₁ t₂ : peano.Term n) := ∃' (↑ₜt₂ ≐ ↑ₜt₁ * #0)
scoped infix:60 (priority := high) " ∣ " => dvd
@[simp] theorem subst_dvd : (t₁ ∣ t₂)[σ]ₚ = t₁[σ]ₜ ∣ t₂[σ]ₜ := by simp [dvd, Term.shift_subst_lift]
@[simp] theorem shift_dvd : ↑ₚ(t₁ ∣ t₂) = ↑ₜt₁ ∣ ↑ₜt₂ := subst_dvd
@[prw] theorem iff_congr_dvd :
  Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ ∣ t₂ ⇔ t₁' ∣ t₂' := by
  pintros 2
  papply iff_congr_exists
  pintro; simp
  prw [0, 1]
  prefl

def prime (t : peano.Term n) := 1 ≺ t ⩑ ∀[≺ t] ((#0 ∣ ↑ₜt) ⇒ #0 ≐ 1)
@[simp] theorem subst_prime : (prime t)[σ]ₚ = prime t[σ]ₜ := by simp [prime, Term.shift_subst_lift]
@[simp] theorem shift_prime : ↑ₚ(prime t) = prime ↑ₜt := subst_prime
@[prw] theorem iff_congr_prime :
  Γ ⊢ t ≐ t' ⇒ prime t ⇔ prime t' := by
  pintro
  papply iff_congr_and
  · prw [0]; prefl
  · papply iff_congr_forall
    pintro; simp
    prw [0]
    prefl

def coprime (t₁ t₂ : peano.Term n) := ∀' (prime #0 ⇒ #0 ∣ ↑ₜt₁ ⇒ ~ #0 ∣ ↑ₜt₂)
@[simp] theorem subst_coprime : (coprime t₁ t₂)[σ]ₚ = coprime t₁[σ]ₜ t₂[σ]ₜ := by simp [coprime, Term.shift_subst_lift]
@[simp] theorem shift_coprime : ↑ₚ(coprime t₁ t₂) = coprime ↑ₜt₁ ↑ₜt₂ := subst_coprime
@[prw] theorem iff_congr_coprime :
  Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ coprime t₁ t₂ ⇔ coprime t₁' t₂' := by
  pintros 2
  papply iff_congr_forall
  pintro; simp
  prw [0, 1]
  prefl

end peano

namespace Theory

open peano Proof

attribute [local simp] Term.shift_subst_single Term.shift_subst_assign Term.shift_subst_cons Term.shift_subst_lift

namespace Q

variable {a b : ℕ}

theorem pair_ofNat : ↑ᵀ^[n] Q ⊢ pair t a b ⇔ t ≐ Nat.pair a b := by
  simp [pair, Nat.pair]
  by_cases h : a < b <;> simp [h]
  · papply iff_intro
    · papply or_elim' <;> prw [and_imp_iff] <;> pintros
      · prw [mul_ofNat, add_ofNat] at 0; passumption
      · papply not_le_ofNat h at 1; papply false_elim; passumption
    · pintro
      papply or_inl
      papply and_intro
      · pexact lt_ofNat h
      · prw [0, mul_ofNat, add_ofNat]; prefl
  · simp at h
    papply iff_intro
    · papply or_elim' <;> prw [and_imp_iff] <;> pintros
      · papply not_lt_ofNat h at 1; papply false_elim; passumption
      · prw [mul_ofNat, add_ofNat, add_ofNat] at 0; passumption
    · pintro
      papply or_inr
      papply and_intro
      · pexact le_ofNat h
      · prw [0, mul_ofNat, add_ofNat, add_ofNat]; prefl

theorem mod_ofNat (hb : 0 < b) : ↑ᵀ^[n] Q ⊢ mod t a b ⇔ t ≐ a % b := by
  simp [mod]
  papply iff_intro
  · rw [←ofNat_succ]
    prw [and_imp_iff, lt_ofNat_iff, bdex_ofNat_iff]
    papply orN_elim'
    intro ⟨i, hi⟩
    pintro
    papply orN_elim'
    intro ⟨j, hj⟩
    pintros; simp
    prw [1] at 0; prw [1]
    by_cases h : j * b + i = a
    · apply congr_arg (· % b) at h
      simp [Nat.mod_eq_of_lt hi] at h
      rw [h]
      prefl
    · prw [mul_ofNat, add_ofNat] at 0
      papply ne_ofNat h at 0
      papply false_elim
      passumption
  · pintro
    papply and_intro
    · prw [0]; pexact lt_ofNat (Nat.mod_lt _ hb)
    · papply exists_intro (a / b); simp
      papply and_intro
      · prw [lt_succ_iff_le]
        pexact le_ofNat (Nat.div_le_self _ _)
      · prw [0, mul_ofNat, add_ofNat]
        simp [Nat.div_add_mod']
        prefl

theorem nmod_ofNat (hb : 0 < b) : ↑ᵀ^[n] Q ⊢ nmod t a b ⇔ ~ t ≐ a % b := by
  simp [nmod]; rw [←ofNat_succ]
  papply iff_intro
  · papply or_elim'
    · pintros
      prw [0] at 1
      papply not_le_ofNat (Nat.mod_lt _ hb) at 1
      passumption
    · prw [bdall_ofNat_iff]; simp
      pintros
      papply andN_elim ⟨a / b, Nat.lt_succ_of_le (Nat.div_le_self _ _)⟩ at 1
      prw [0, mul_ofNat, add_ofNat] at 1; simp [Nat.div_add_mod']
      papplya 1
      prefl
  · pintro
    prw [←not_lt_ofNat_iff, ←imp_iff, lt_ofNat_iff, bdall_ofNat_iff]
    papply orN_elim'
    intro ⟨i, hi⟩
    pintro
    apply andN_intro
    intro ⟨j, hj⟩
    pintros; simp
    prw [1] at 2; prw [1, mul_ofNat, add_ofNat] at 0
    by_cases h : j * b + i = a
    · apply congr_arg (· % b) at h
      simp [Nat.mod_eq_of_lt hi] at h
      rw [h]
      papplya 2
      prefl
    · papply ne_ofNat h at 0
      passumption

theorem beta_ofNat : ↑ᵀ^[n] Q ⊢ beta t a b ⇔ t ≐ Nat.beta a b := by
  simp [beta, Nat.beta]
  papply iff_intro
  · rw [←ofNat_succ]
    prw [bdex_ofNat_iff]
    papply orN_elim'
    intro ⟨i, hi⟩; simp [←ofNat_succ]
    prw [bdex_ofNat_iff]
    papply orN_elim'
    intro ⟨j, hj⟩; simp
    prw [and_imp_iff, pair_ofNat]
    pintros
    by_cases h : a = Nat.pair i j
    · simp [h, ←ofNat_succ]
      prw [mul_ofNat] at 0
      rw [←ofNat_succ]
      prw [mod_ofNat (Nat.zero_lt_succ _)] at 0
      passumption
    · papply ne_ofNat h at 1
      papply false_elim
      passumption
  · pintro
    papply exists_intro a.unpair.1; simp
    papply and_intro
    · pexact lt_ofNat (Nat.lt_succ_of_le (Nat.unpair_left_le _))
    · papply exists_intro a.unpair.2; simp
      papply and_intro
      · pexact lt_ofNat (Nat.lt_succ_of_le (Nat.unpair_right_le _))
      papply and_intro
      · prw [pair_ofNat]; simp; prefl
      · rw [←ofNat_succ]; prw [mul_ofNat]; rw [←ofNat_succ]; prw [mod_ofNat (Nat.zero_lt_succ _)]; passumption

theorem nbeta_ofNat : ↑ᵀ^[n] Q ⊢ nbeta t a b ⇔ ~ t ≐ Nat.beta a b := by
  simp [nbeta, Nat.beta]
  papply iff_intro
  · rw [←ofNat_succ]
    prw [bdex_ofNat_iff]
    papply orN_elim'
    intro ⟨i, hi⟩; simp [←ofNat_succ]
    prw [bdex_ofNat_iff]
    papply orN_elim'
    intro ⟨j, hj⟩; simp
    prw [and_imp_iff, pair_ofNat]
    pintros
    by_cases h : a = Nat.pair i j
    · simp [h, ←ofNat_succ]
      prw [mul_ofNat] at 1
      rw [←ofNat_succ]
      prw [nmod_ofNat (Nat.zero_lt_succ _)] at 1
      papplya 1
      passumption
    · papply ne_ofNat h at 2
      passumption
  · pintro
    papply exists_intro a.unpair.1; simp
    papply and_intro
    · pexact lt_ofNat (Nat.lt_succ_of_le (Nat.unpair_left_le _))
    · papply exists_intro a.unpair.2; simp
      papply and_intro
      · pexact lt_ofNat (Nat.lt_succ_of_le (Nat.unpair_right_le _))
      papply and_intro
      · prw [pair_ofNat]; simp; prefl
      · rw [←ofNat_succ]; prw [mul_ofNat]; rw [←ofNat_succ]; prw [nmod_ofNat (Nat.zero_lt_succ _)]; passumption

end Q

open Q

namespace PA

theorem pair_unique : ↑ᵀ^[n] PA ⊢ pair t t₁ t₂ ⇒ pair t' t₁ t₂ ⇒ t ≐ t' := by
  papply or_elim' <;> prw [and_imp_iff] <;> pintros 2
  · papply or_elim' <;> prw [and_imp_iff] <;> pintros
    · prw [0, 2]; prefl
    · prw [←LO.neg_le_iff] at 3
      papplya 3 at 1
      papply false_elim
      passumption
  · papply or_elim' <;> prw [and_imp_iff] <;> pintros
    · prw [←LO.neg_lt_iff] at 3
      papplya 3 at 1
      papply false_elim
      passumption
    · prw [0, 2]; prefl

theorem pair_total (t₁ t₂) : ↑ᵀ^[n] PA ⊢ ∃' (pair #0 ↑ₜt₁ ↑ₜt₂) := by
  papply or_elim
  · pexact LO.lt_or_ge t₁ t₂
  · pintro
    papply exists_intro (t₂ * t₂ + t₁); simp [pair]
    papply or_inl
    papply and_intro
    · passumption
    · prefl
  · pintro
    papply exists_intro (t₁ * t₁ + t₁ + t₂); simp [pair]
    papply or_inr
    papply and_intro
    · passumption
    · prefl

theorem add_le_pair : ↑ᵀ^[n] PA ⊢ pair t t₁ t₂ ⇒ t₁ + t₂ ⪯ t := by
  papply or_elim'
  · prw [and_imp_iff]
    pintros 2
    prw [0, add_comm t₁ t₂, add_le_add_iff_right]
    papply le_mul_left
    papply pos_of_lt
    passumption
  · prw [and_imp_iff]
    pintros 2
    prw [0, add_le_add_iff_right]
    pexact le_add_left

theorem left_le_pair : ↑ᵀ^[n] PA ⊢ pair t t₁ t₂ ⇒ t₁ ⪯ t := by
  pintro
  papply PO.le_trans
  · pexact le_add_right
  · papply add_le_pair; passumption

theorem right_le_pair : ↑ᵀ^[n] PA ⊢ pair t t₁ t₂ ⇒ t₂ ⪯ t := by
  pintro
  papply PO.le_trans
  · pexact le_add_left
  · papply add_le_pair; passumption

theorem exists_sqrt (t) : ↑ᵀ^[n] PA ⊢ ∃' (#0 * #0 ⪯ ↑ₜt ⩑ ↑ₜt ≺ S #0 * S #0) := by
  psuffices ∀' ∃' (#0 * #0 ⪯ #1 ⩑ #1 ≺ S #0 * S #0)
  · papply forall_elim t at 0; simp; passumption
  · papply ind <;> simp
    · papply exists_intro 0; simp
      papply and_intro
      · prw [mul_zero]; pexact PO.le_refl
      · prw [mul_succ, add_succ]
        pexact zero_lt_succ
    · pintro
      papply exists_elim'
      pintro
      prw [and_imp_iff]
      pintro
      prw [mul_succ, add_succ, lt_succ_iff_lt_or_eq]
      papply or_elim'
      · pintro
        papply exists_intro #0; simp [Subst.single]
        papply and_intro
        · papply le_succ_of_le
          passumption
        · prw [mul_succ, add_succ, succ_lt_succ_iff]
          passumption
      · pintro
        papply exists_intro (S #0); simp [Subst.single]
        papply and_intro
        · prw [0, mul_succ, add_succ]
          pexact PO.le_refl
        · prw [0, mul_succ, add_succ, succ_lt_succ_iff, add_succ, lt_succ_iff_le, add_le_add_iff_right]
          papply mul_le_mul <;> pexact le_succ_self

theorem exists_unpair (t) : ↑ᵀ^[n] PA ⊢ ∃' ∃' (pair ↑ₜ↑ₜt #1 #0) := by
  papply exists_elim
  · pexact exists_sqrt t
  · pintro; prw [and_imp_iff]; pintros 2
    papply or_elim
    · pexact LO.le_or_gt (#0 * #0 + #0) ↑ₜt
    · papply exists_elim'
      pintros 2; simp
      papply exists_intro #1
      papply exists_intro #0; simp [Term.shift_subst_cons, Subst.single, ←Term.shift_def]
      papply or_inr
      papply and_intro
      · prw [←0, mul_succ, succ_mul, add_comm _ (S #1), add_lt_add_iff_right, lt_succ_iff_le] at 1
        passumption
      · prw [←0, add_comm #0]
        prefl
    · pintro
      papply exists_elim
      · passumption 2
      · pintros 2; simp
        papply exists_intro #0
        papply exists_intro #1; simp [←Term.shift_def]
        papply or_inl
        papply and_intro
        · prw [←0, add_comm #0, add_lt_add_iff_left] at 1
          passumption
        · prw [←0, add_comm #0]
          prefl

-- Unfortuantely we don't have a "wlog" tactic yet...
theorem unpair_unique : ↑ᵀ^[n] PA ⊢ pair t t₁ t₂ ⇒ pair t t₃ t₄ ⇒ t₁ ≐ t₃ ⩑ t₂ ≐ t₄ := by
  papply or_elim'
  · prw [and_imp_iff]
    pintros 2
    papply or_elim'
    · prw [and_imp_iff]
      pintros 2
      phave t₂ ≐ t₄
      · prw [←double_neg_iff, LO.ne_iff_lt_or_gt]
        papply or_elim' <;> pintro <;> prw [←succ_le_iff_lt] at 0
        · psuffices t₂ * t₂ + t₁ ≺ t₄ * t₄ + t₃
          · prw [←2, ←4] at 0
            papply PO.lt_irrefl at 0
            passumption
          · papply lt_add_of_lt_right
            papply PO.lt_of_le_of_lt'
            · papply mul_le_mul <;> passumption 0
            · prw [←succ_le_iff_lt, succ_mul, add_succ, succ_le_succ_iff]
              papply add_le_add
              · papply mul_le_mul_left; pexact le_succ_self
              · papply PO.le_of_lt; passumption
        · psuffices t₄ * t₄ + t₃ ≺ t₂ * t₂ + t₁
          · prw [←2, ←4] at 0
            papply PO.lt_irrefl at 0
            passumption
          · papply lt_add_of_lt_right
            papply PO.lt_of_le_of_lt'
            · papply mul_le_mul <;> passumption 0
            · prw [←succ_le_iff_lt, succ_mul, add_succ, succ_le_succ_iff]
              papply add_le_add
              · papply mul_le_mul_left; pexact le_succ_self
              · papply PO.le_of_lt; passumption
      · prw [←0, 3] at 1
        papply add_left_cancel at 1
        papply and_intro <;> passumption
    · prw [and_imp_iff]
      pintros 2
      phave t₂ ⪯ t₃
      · pcontra
        prw [LO.neg_le_iff, ←succ_le_iff_lt] at 0
        psuffices t₃ * t₃ + t₃ + t₄ ≺ t₂ * t₂ + t₁
        · prw [←2, ←4] at 0
          papply PO.lt_irrefl at 0
          passumption
        · papply lt_add_of_lt_right
          papply PO.lt_of_le_of_lt'
          · papply mul_le_mul <;> passumption
          · prw [←succ_le_iff_lt, succ_mul, mul_succ, add_succ, succ_le_succ_iff, add_le_add_iff_left]
            passumption
      · psuffices t₂ * t₂ + t₁ ≺ t₃ * t₃ + t₃ + t₄
        · prw [←2, ←4] at 0
          papply PO.lt_irrefl at 0
          papply false_elim
          passumption
        · prw [←succ_le_iff_lt, ←add_succ, add_assoc]
          papply add_le_add
          · papply mul_le_mul <;> passumption
          · papply le_add_of_le_right
            prw [succ_le_iff_lt]
            papply PO.lt_of_lt_of_le <;> passumption
  · prw [and_imp_iff]
    pintros 2
    papply or_elim'
    · prw [and_imp_iff]
      pintros 2
      phave t₄ ⪯ t₁
      · pcontra
        prw [LO.neg_le_iff, ←succ_le_iff_lt] at 0
        psuffices t₁ * t₁ + t₁ + t₂ ≺ t₄ * t₄ + t₃
        · prw [←2, ←4] at 0
          papply PO.lt_irrefl at 0
          passumption
        · papply lt_add_of_lt_right
          papply PO.lt_of_le_of_lt'
          · papply mul_le_mul <;> passumption
          · prw [←succ_le_iff_lt, succ_mul, mul_succ, add_succ, succ_le_succ_iff, add_le_add_iff_left]
            passumption
      · psuffices t₄ * t₄ + t₃ ≺ t₁ * t₁ + t₁ + t₂
        · prw [←2, ←4] at 0
          papply PO.lt_irrefl at 0
          papply false_elim
          passumption
        · prw [←succ_le_iff_lt, ←add_succ, add_assoc]
          papply add_le_add
          · papply mul_le_mul <;> passumption
          · papply le_add_of_le_right
            prw [succ_le_iff_lt]
            papply PO.lt_of_lt_of_le <;> passumption
    · prw [and_imp_iff]
      pintros 2
      phave t₁ ≐ t₃
      · prw [←double_neg_iff, LO.ne_iff_lt_or_gt]
        papply or_elim' <;> pintro <;> prw [←succ_le_iff_lt] at 0
        · psuffices t₁ * t₁ + t₁ + t₂ ≺ t₃ * t₃ + t₃ + t₄
          · prw [←2, ←4] at 0
            papply PO.lt_irrefl at 0
            passumption
          · papply lt_add_of_lt_right
            papply PO.lt_of_le_of_lt'
            · papply add_le_add
              · papply mul_le_mul <;> passumption 0
              · passumption 0
            · prw [←succ_le_iff_lt, succ_mul, add_succ, succ_le_succ_iff]
              papply add_le_add
              · papply add_le_add
                · papply mul_le_mul_left; pexact le_succ_self
                · pexact le_succ_self
              · passumption
        · psuffices t₃ * t₃ + t₃ + t₄ ≺ t₁ * t₁ + t₁ + t₂
          · prw [←2, ←4] at 0
            papply PO.lt_irrefl at 0
            passumption
          · papply lt_add_of_lt_right
            papply PO.lt_of_le_of_lt'
            · papply add_le_add
              · papply mul_le_mul <;> passumption 0
              · passumption 0
            · prw [←succ_le_iff_lt, succ_mul, add_succ, succ_le_succ_iff]
              papply add_le_add
              · papply add_le_add
                · papply mul_le_mul_left; pexact le_succ_self
                · pexact le_succ_self
              · passumption
      · prw [←0, 3] at 1
        papply add_left_cancel at 1
        papply and_intro <;> passumption

theorem mod_unique : ↑ᵀ^[n] PA ⊢ mod t t₁ t₂ ⇒ mod t' t₁ t₂ ⇒ t ≐ t' := by
  simp [mod]
  prw [and_imp_iff]
  pintro
  papply exists_elim'
  pintro; simp
  prw [and_imp_iff, and_imp_iff]
  pintros 3
  papply exists_elim'
  pintro; simp [←Term.shift_def]
  prw [and_imp_iff]
  pintros
  psuffices #0 ≐ #1
  · prw [0, ←4] at 1
    papply add_left_cancel at 1
    prw [1]
    prefl
  · prw [←double_neg_iff, LO.ne_iff_lt_or_gt]
    papply or_elim'
    · papply exists_elim'
      pintros; simp
      prw [←0, ←1, add_succ, ←succ_add, add_comm (S #0), right_distrib, add_assoc] at 4
      papply add_left_cancel at 4
      prw [←add_zero ↑ₜ↑ₜ↑ₜt₂, ←4, succ_mul, add_comm (_ * _), add_assoc, add_lt_add_iff_left] at 3
      papply not_lt_zero at 3
      passumption
    · papply exists_elim'
      pintros; simp
      prw [←0, ←4, add_succ, ←succ_add, add_comm (S #0), right_distrib, add_assoc] at 1
      papply add_left_cancel at 1
      prw [←add_zero ↑ₜ↑ₜ↑ₜt₂, ←1, succ_mul, add_comm (_ * _), add_assoc, add_lt_add_iff_left] at 6
      papply not_lt_zero at 6
      passumption

theorem self_mod_of_lt : ↑ᵀ^[n] PA ⊢ t₁ ≺ t₂ ⇒ mod t₁ t₁ t₂ := by
  pintro
  papply and_intro
  · passumption
  · papply exists_intro 0; simp [Term.shift_subst_single]
    papply and_intro
    · pexact zero_lt_succ
    · prw [zero_mul, zero_add]; prefl

theorem add_mod_iff : ↑ᵀ^[n] PA ⊢ mod t (t₁ + t₂) t₂ ⇔ mod t t₁ t₂ := by
  papply iff_intro
  · rw [mod]; prw [and_imp_iff]
    pintro
    papply exists_elim'
    pintro
    prw [and_imp_iff]
    pintros 2; simp
    papply and_intro
    · passumption
    · papply or_elim
      · pexact zero_or_succ #0
      · pintro
        prw [0, zero_mul, zero_add, Proof.eq_comm] at 1
        papply le_of_add_eq at 1
        papply PO.not_ge_of_lt at 3
        papplya 3 at 1
        papply false_elim
        passumption
      · papply exists_elim'
        pintros 2
        papply exists_intro #0; simp [←Term.shift_def]
        papply and_intro
        · prw [0, succ_mul, add_right_comm] at 1
          papply add_right_cancel at 1
          pcontra
          prw [LO.neg_lt_iff, succ_le_iff_lt, ←2] at 0
          papply PO.lt_irrefl
          papply PO.lt_of_lt_of_le'
          · passumption 0
          · papply le_add_of_le_right
            papply le_mul_right
            papply pos_of_lt
            passumption 4
        · prw [0, succ_mul, add_right_comm] at 1
          papply add_right_cancel at 1
          passumption
  · rw [mod]; prw [and_imp_iff]
    pintro
    papply exists_elim'
    pintro; simp
    prw [and_imp_iff]
    pintros 2
    papply and_intro
    · passumption
    · papply exists_intro (S #0); simp
      papply and_intro
      · prw [succ_lt_succ_iff]
        papply PO.lt_of_le_of_lt
        · prw [←lt_succ_iff_le]; passumption 1
        · papply PO.lt_of_le_of_lt
          · papply le_add_right
          · prw [add_lt_add_iff_left]
            passumption 2
      · prw [←0, add_right_comm, succ_mul]
        prefl

theorem add_mul_mod_iff : ↑ᵀ^[n] PA ⊢ mod t (t₁ + t₂ * t₃) t₂ ⇔ mod t t₁ t₂ := by
  psuffices ∀' (mod ↑ₜt (↑ₜt₁ + ↑ₜt₂ * #0) ↑ₜt₂ ⇔ mod ↑ₜt ↑ₜt₁ ↑ₜt₂)
  · papply forall_elim t₃ at 0; simp; passumption
  · papply ind <;> simp
    · prw [mul_zero, add_zero]; prefl
    · pintros 2; prw [mul_succ, ←add_assoc, add_mod_iff, 0]; prefl

theorem mod_total (t₁ t₂) : ↑ᵀ^[n] PA ⊢ 0 ≺ t₂ ⇒ ∃' (mod #0 ↑ₜt₁ ↑ₜt₂) := by
  pintro
  psuffices ∀' ∃' (mod #0 #1 ↑ₜ↑ₜt₂)
  · papply forall_elim t₁ at 0; simp [Term.shift_subst_lift, Term.shift_subst_single]; passumption
  · papply strong_ind
    simp [Term.shift, ←Term.subst_comp, Subst.comp_def]
    pintros 2
    papply or_elim
    · pexact LO.lt_or_ge #0 ↑ₜt₂
    · pintro
      papply exists_intro #0; simp [←Term.subst_comp, Subst.comp_def]; rw [←Subst.shift_def, ←Term.shift_def]
      papply self_mod_of_lt
      passumption 0
    · papply exists_elim'
      pintro; simp [Term.shift, Formula.shift, ←Term.subst_comp, Subst.comp_def]
      pintro
      papply forall_elim #0 at 1; simp [←Term.subst_comp, Subst.comp_def, Subst.single]
      papply exists_elim
      · papplya 1
        prw [←add_lt_add_iff_right (t := #0), zero_add, add_comm, 0] at 2
        passumption
      · pintros 2; simp [Term.shift, ←Term.subst_comp, Subst.comp_def]
        prw [←add_mod_iff, 1] at 0
        papply exists_intro #0; simp [Subst.single, ←Term.subst_comp, Subst.comp_def]
        passumption

theorem nmod_iff : ↑ᵀ^[n] PA ⊢ nmod t t₁ t₂ ⇔ ~ mod t t₁ t₂ := by
  simp [nmod, mod]
  prw [neg_and_iff, Order.neg_bdex_iff, LO.neg_lt_iff]
  prefl

theorem beta_unique : ↑ᵀ^[n] PA ⊢ beta t t₁ t₂ ⇒ beta t' t₁ t₂ ⇒ t ≐ t' := by
  simp [beta]
  papply exists_elim'
  · pintro
    prw [and_imp_iff]
    pintro
    papply exists_elim'
    pintro
    prw [and_imp_iff, and_imp_iff]
    pintros 3
    papply exists_elim'
    pintro; simp [Term.shift_subst_lift]; repeat rw [←Term.shift]
    prw [and_imp_iff]
    pintro
    papply exists_elim'
    pintro
    prw [and_imp_iff, and_imp_iff]
    pintros; simp
    phave #0 ≐ #2 ⩑ #1 ≐ #3
    · prw [Proof.and_comm]; papply unpair_unique <;> passumption
    · prevert; prw [and_imp_iff]; pintros
      papply mod_unique
      · passumption 6
      · prw [←0, ←1]; passumption

theorem beta_total (t₁ t₂) : ↑ᵀ^[n] PA ⊢ ∃' (beta #0 ↑ₜt₁ ↑ₜt₂) := by
  papply exists_elim
  · pexact exists_unpair t₁
  · pintro
    papply exists_elim'
    pintros 2; simp [Formula.shift, Term.shift_subst_lift]; repeat rw [←Term.shift]
    papply exists_elim
    · papply mod_total #1 (S (S ↑ₜ↑ₜt₂ * #0))
      pexact zero_lt_succ
    · pintros 2
      papply exists_intro #0; simp [Term.shift_subst_lift, Term.shift_subst_single]; repeat rw [←Term.shift]
      papply exists_intro #2; simp [Term.shift_subst_lift, Term.shift_subst_single]
      papply and_intro
      · prw [lt_succ_iff_le]
        papply left_le_pair
        passumption
      · papply exists_intro #1; simp [Term.shift_subst_single]; simp [Subst.single]
        papply and_intro
        · prw [lt_succ_iff_le]
          papply right_le_pair
          passumption
        · papply and_intro <;> passumption

theorem nbeta_iff : ↑ᵀ^[n] PA ⊢ nbeta t t₁ t₂ ⇔ ~ beta t t₁ t₂ := by
  papply iff_intro
  · papply exists_elim'
    pintro
    prw [and_imp_iff]
    pintro
    papply exists_elim'
    pintro
    prw [and_imp_iff, and_imp_iff]
    pintros 3
    papply exists_elim'
    pintro; simp [Term.shift_subst_lift]; repeat rw [←Term.shift]
    prw [neg_and_iff, ←imp_iff]
    pintro
    papply exists_elim'
    pintro; simp
    prw [neg_and_iff, ←imp_iff, neg_and_iff, ←imp_iff]
    pintros
    phave #1 ≐ #3 ⩑ #0 ≐ #2
    · papply unpair_unique <;> passumption
    · prevert; prw [and_imp_iff]; pintros
      prw [0, 1] at 2
      prw [nmod_iff] at 6
      papplya 6 at 2
      passumption
  · papply exists_elim
    · pexact exists_unpair t₁
    · pintro
      papply exists_elim'
      pintros 2; simp; pintro
      papply exists_intro #1; simp [Term.shift_subst_single]
      papply and_intro
      · prw [lt_succ_iff_le]; papply left_le_pair; passumption
      · papply exists_intro #0; simp [Term.shift_subst_single]; simp [Subst.single]
        papply and_intro
        · prw [lt_succ_iff_le]; papply right_le_pair; passumption
        papply and_intro
        · passumption
        · prw [nmod_iff]
          pintro
          papplya 1
          papply exists_intro #1; simp [Term.shift_subst_single]
          papply and_intro
          · prw [lt_succ_iff_le]; papply left_le_pair; passumption
          · papply exists_intro #0; simp [Term.shift_subst_single]; simp [Subst.single]
            papply and_intro
            · prw [lt_succ_iff_le]; papply right_le_pair; passumption
            papply and_intro
            · passumption
            · passumption

theorem le_of_dvd : ↑ᵀ^[n] PA ⊢ 0 ≺ t₂ ⇒ t₁ ∣ t₂ ⇒ t₁ ⪯ t₂ := by
  pintro; papply exists_elim'; pintros 2; simp
  prw [0, mul_pos_iff] at 1
  prw [←mul_one ↑ₜt₁, 0]
  papply mul_le_mul_left
  prw [one_le_iff_zero_lt]
  papply and_right at 1
  passumption

theorem dvd_refl : ↑ᵀ^[n] PA ⊢ t ∣ t := by
  papply exists_intro 1; simp
  prw [mul_one]
  prefl

theorem dvd_trans : ↑ᵀ^[n] PA ⊢ t₁ ∣ t₂ ⇒ t₂ ∣ t₃ ⇒ t₁ ∣ t₃ := by
  papply exists_elim'; pintros 2
  papply exists_elim'; pintros 2
  papply exists_intro (#1 * #0); simp [←Term.shift_def]
  prw [←mul_assoc, ←1, ←0]
  prefl

theorem dvd_zero : ↑ᵀ^[n] PA ⊢ t ∣ 0 := by
  papply exists_intro 0; simp; prw [mul_zero]; prefl

theorem zero_dvd_iff_eq_zero : ↑ᵀ^[n] PA ⊢ 0 ∣ t ⇔ t ≐ 0 := by
  papply iff_intro
  · papply exists_elim'; pintros 2; simp
    prw [zero_mul] at 0
    passumption
  · pintro; prw [0]; pexact dvd_refl

theorem one_dvd : ↑ᵀ^[n] PA ⊢ 1 ∣ t := by
  papply exists_intro t; simp
  prw [one_mul]; prefl

theorem dvd_mul_of_dvd_left : ↑ᵀ^[n] PA ⊢ t ∣ t₁ ⇒ t ∣ t₂ * t₁ := by
  papply exists_elim'; pintros 2; simp
  papply exists_intro (#0 * ↑ₜt₂); simp
  prw [←mul_assoc, ←0]
  pexact mul_comm

theorem dvd_mul_of_dvd_right : ↑ᵀ^[n] PA ⊢ t ∣ t₁ ⇒ t ∣ t₁ * t₂ := by
  prw [mul_comm]; pexact dvd_mul_of_dvd_left

theorem dvd_mul_left : ↑ᵀ^[n] PA ⊢ t ∣ t' * t := by
  papply dvd_mul_of_dvd_left; pexact dvd_refl

theorem dvd_mul_right : ↑ᵀ^[n] PA ⊢ t ∣ t * t' := by
  papply dvd_mul_of_dvd_right; pexact dvd_refl

theorem dvd_one_iff_eq_one : ↑ᵀ^[n] PA ⊢ t ∣ 1 ⇔ t ≐ 1 := by
  papply iff_intro
  · papply exists_elim'; pintros 2; simp
    prw [Proof.eq_comm, mul_eq_one_iff] at 0
    papply and_left at 0
    passumption
  · pintro; prw [0]; pexact dvd_refl

theorem dvd_add_iff_left : ↑ᵀ^[n] PA ⊢ t ∣ t₁ ⇒ t ∣ t₁ + t₂ ⇔ t ∣ t₂ := by
  papply exists_elim'
  pintros 2; simp
  prw [0]
  papply iff_intro
  · papply or_elim
    · pexact zero_or_pos ↑ₜt
    · pintros 2
      prw [1, zero_mul, zero_add, zero_dvd_iff_eq_zero] at 0
      prw [1, 0]
      pexact dvd_refl
    · pintro
      papply exists_elim'
      pintros 2; simp
      phave #1 ⪯ #0
      · prw [←mul_le_mul_iff_left]
        · prw [←0]; pexact le_add_right
        · passumption
      prevert; papply exists_elim'; pintros 2; simp
      prw [←0, add_comm #0, left_distrib] at 1
      papply add_left_cancel at 1
      papply exists_intro #0; simp
      passumption
  · papply exists_elim'; pintros 2; simp
    papply exists_intro (#1 + #0); simp [Subst.single]
    prw [left_distrib, ←1, ←0]
    prefl

theorem dvd_add_iff_right : ↑ᵀ^[n] PA ⊢ t ∣ t₂ ⇒ t ∣ t₁ + t₂ ⇔ t ∣ t₁ := by
  prw [add_comm]; pexact dvd_add_iff_left

theorem prime_gt_one : ↑ᵀ^[n] PA ⊢ prime t ⇒ 1 ≺ t := by
  pexact and_left

theorem dvd_prime_iff : ↑ᵀ^[n] PA ⊢ prime t ⇒ t' ∣ t ⇔ t' ≐ 1 ⩒ t' ≐ t := by
  pintro
  papply iff_intro
  · pintros 2
    pcontra
    prw [LO.ne_iff_lt_or_gt] at 0
    prevert; papply or_elim'
    · pintro
      papplya 1
      papply and_right at 3
      papply forall_elim t' at 3; simp
      papplya 3 <;> passumption
    · pintro
      papply le_of_dvd at 2
      · papply PO.not_ge_of_lt <;> passumption
      · papply prime_gt_one at 3
        papply PO.lt_trans'
        · passumption 3
        · pexact zero_lt_succ
  · papply or_elim'
    · pintro; prw [0]; pexact one_dvd
    · pintro; prw [0]; pexact dvd_refl

theorem exists_prime_dvd_of_gt_one (t) : ↑ᵀ^[n] PA ⊢ 1 ≺ t ⇒ ∃' (prime #0 ⩑ #0 ∣ ↑ₜt) := by
  pintro
  phave ∃' (1 ≺ #0 ⩑ #0 ∣ ↑ₜt)
  · papply exists_intro t; simp
    papply and_intro
    · passumption
    · pexact dvd_refl
  papply exists_min at 0; simp
  prevert; papply exists_elim'; pintro; prw [and_imp_iff, and_imp_iff]; pintros 3
  papply exists_intro #0; simp
  papply and_intro
  · papply and_intro
    · passumption
    · pintros
      pcontra
      prw [LO.ne_iff_lt_or_gt] at 0
      prevert; papply or_elim'
      · pintro; simp [one_def]; prw [lt_succ_iff_le, le_zero_iff_eq_zero] at 0
        prw [0, zero_dvd_iff_eq_zero] at 1
        prw [0, 1] at 2
        papply PO.lt_irrefl at 2; passumption
      · pintro
        papply forall_elim #0 at 3; simp [Term.shift, ←Term.subst_comp, Subst.comp_def, Subst.single]
        papplya 3
        · passumption
        · papply and_intro
          · passumption
          · papply dvd_trans <;> passumption
  · passumption

theorem coprime_irrefl_of_gt_one : ↑ᵀ^[n] PA ⊢ 1 ≺ t ⇒ ~ coprime t t := by
  pintro
  papply exists_prime_dvd_of_gt_one at 0
  prevert; papply exists_elim'; pintro; simp
  prw [and_imp_iff]; pintros
  papply forall_elim #0 at 0; simp
  papplya 0 <;> passumption

theorem coprime_symm : ↑ᵀ^[n] PA ⊢ coprime t₁ t₂ ⇒ coprime t₂ t₁ := by
  pintros; simp
  papply forall_elim #0 at 3; simp
  papplya 3 <;> passumption

theorem coprime_comm : ↑ᵀ^[n] PA ⊢ coprime t₁ t₂ ⇔ coprime t₂ t₁ := by
  papply iff_intro <;> pexact coprime_symm

theorem coprime_add_iff_left : ↑ᵀ^[n] PA ⊢ coprime (t₂ + t₁) t₂ ⇔ coprime t₁ t₂ := by
  papply iff_congr_forall
  pintro; simp
  papply iff_intro
  · pintros; papplya 3
    · passumption
    · prw [dvd_add_iff_right] <;> passumption
    · passumption
  · pintros; papplya 3
    · passumption
    · prw [dvd_add_iff_left] at 1 <;> passumption
    · passumption

theorem coprime_add_iff_right : ↑ᵀ^[n] PA ⊢ coprime (t₁ + t₂) t₂ ⇔ coprime t₁ t₂ := by
  prw [add_comm]; pexact coprime_add_iff_left

theorem coprime_bezout : ↑ᵀ^[n] PA ⊢ 0 ≺ t₁ ⇒ 0 ≺ t₂ ⇒ coprime t₁ t₂ ⇒ ∃' ∃' (↑ₜ↑ₜt₁ * #1 ≐ S (↑ₜ↑ₜt₂ * #0)) := by
  psuffices ∀' ∀' ∀' (#1 + #0 ⪯ #2 ⇒ 0 ≺ #1 ⇒ 0 ≺ #0 ⇒ coprime #1 #0 ⇒ ∃' ∃' (#3 * #1 ≐ S (#2 * #0)))
  · papply forall_elim (t₁ + t₂) at 0
    papply forall_elim t₁ at 0
    papply forall_elim t₂ at 0
    simp [Term.shift, ←Term.subst_comp, Subst.comp_def, Subst.lift]; rw [←Subst.id_def]; simp [Term.subst_id]
    pintros 3
    papplya 3
    · pexact PO.le_refl
    · passumption 2
    · passumption 1
    · passumption 0
  · papply strong_ind
    pintros 8; simp [Formula.shift, Subst.lift]
    papply or_elim
    · pexact LO.lt_trichotomy #1 #0
    · papply exists_elim'; pintros 2; simp [Formula.shift, Subst.lift]
      papply exists_elim
      · papply forall_elim #1 at 5; simp [Subst.lift, Subst.single]
        pspecialize 5 with 1
        · papply PO.lt_of_le_of_lt'
          · passumption 4
          · papply lt_add_of_pos_left
            passumption 3
        papply forall_elim #2 at 5
        papply forall_elim (S #0) at 5
        simp [Subst.lift, Subst.single]
        papplya 5
        · prw [add_succ, ←succ_add, add_comm, 0]; pexact PO.le_refl
        · passumption 3
        · pexact zero_lt_succ
        · prw [coprime_comm, ←coprime_add_iff_right, succ_add, ←add_succ, 0, coprime_comm]; passumption 1
      pintro; papply exists_elim'; pintros 2; simp [Formula.shift, Subst.lift]
      papply exists_intro (#1 + #0)
      papply exists_intro #0
      simp [Subst.lift, Subst.single]
      prw [left_distrib, 0, succ_mul, succ_add, add_right_comm, ←1, right_distrib, succ_mul, ←add_assoc]
      prefl
    papply or_elim'
    · pintro
      prw [←succ_le_iff_lt, PO.le_iff_lt_or_eq] at 2
      prevert 2; rw [←one_def]; papply or_elim'
      · pintro
        papply false_elim
        papply coprime_irrefl_of_gt_one
        · passumption 0
        · prw [1] at 2; passumption 2
      · pintro
        papply exists_intro 1
        papply exists_intro 0
        simp [Subst.lift, Subst.single]
        prw [1, ←0, one_mul]
        prefl
    · papply exists_elim'; pintros 2; simp [Formula.shift, Subst.lift]
      papply exists_elim
      · papply forall_elim #2 at 5; simp [Subst.lift, Subst.single]
        pspecialize 5 with 1
        · papply PO.lt_of_le_of_lt'
          · passumption 4
          · papply lt_add_of_pos_right
            passumption 2
        papply forall_elim (S #0) at 5
        papply forall_elim #1 at 5
        simp [Subst.lift, Subst.single]
        papplya 5
        · prw [succ_add, ←add_succ, 0]; pexact PO.le_refl
        · pexact zero_lt_succ
        · passumption 2
        · prw [←coprime_add_iff_right, succ_add, ←add_succ, 0]; passumption 1
      pintro; papply exists_elim'; pintros 2; simp [Formula.shift, Subst.lift]
      papply exists_intro #1
      papply exists_intro (#0 + #1)
      simp [Subst.lift, Subst.single]
      prw [←1, right_distrib, succ_mul, ←add_assoc, left_distrib, ←succ_add, ←0, succ_mul]
      pexact add_right_comm

theorem prime_dvd_prime_iff_eq : ↑ᵀ^[n] PA ⊢ prime t₁ ⇒ prime t₂ ⇒ t₁ ∣ t₂ ⇔ t₁ ≐ t₂ := by
  pintros 2
  papply iff_intro
  · prw [dvd_prime_iff]
    · papply or_elim'
      · pintro
        prw [0] at 2
        papply prime_gt_one at 2
        papply PO.lt_irrefl at 2
        papply false_elim
        passumption
      · pintro; passumption
    · passumption
  · pintro; prw [0]; pexact dvd_refl

theorem coprime_prime_iff : ↑ᵀ^[n] PA ⊢ prime t ⇒ coprime t t' ⇔ ~ t ∣ t' := by
  pintro
  papply iff_intro
  · pintros
    papply forall_elim t at 1; simp
    papplya 1
    · passumption
    · pexact dvd_refl
    · passumption
  · pintros; simp
    prw [prime_dvd_prime_iff_eq] at 1
    · prw [1] at 0; papplya 3; passumption
    · passumption
    · passumption

theorem dvd_mul_coprime : ↑ᵀ^[n] PA ⊢ 0 ≺ t ⇒ 0 ≺ t₁ ⇒ coprime t t₁ ⇒ t ∣ t₁ * t₂ ⇒ t ∣ t₂ := by
  pintros 4
  papply coprime_symm at 1
  papply coprime_bezout at 1
  · prevert 1; papply exists_elim'; pintro
    papply exists_elim'; pintros 2; simp
    papply dvd_mul_of_dvd_right (t₂ := #1) at 1
    prw [mul_right_comm, 0, succ_mul, dvd_add_iff_left] at 1
    · passumption
    · papply dvd_mul_of_dvd_right; pexact dvd_mul_right
  · passumption
  · passumption

theorem prime_dvd_mul_iff : ↑ᵀ^[n] PA ⊢ prime t ⇒ t ∣ t₁ * t₂ ⇔ t ∣ t₁ ⩒ t ∣ t₂ := by
  pintro
  papply iff_intro
  · pintro
    pcontra
    prw [neg_or_iff] at 0
    papply dvd_mul_coprime at 1
    · papply and_right at 0; papplya 0; passumption
    · papply prime_gt_one at 2
      papply PO.lt_trans
      · pexact zero_lt_succ
      · passumption 2
    · pcontra
      prw [LO.neg_lt_iff, le_zero_iff_eq_zero] at 0
      papply and_left at 1
      papplya 1
      prw [0]
      pexact dvd_zero
    · prw [coprime_prime_iff]
      · papply and_left at 0; passumption
      · passumption
  · papply or_elim'
    · pexact dvd_mul_of_dvd_right
    · pexact dvd_mul_of_dvd_left

theorem dvd_mul_prime : ↑ᵀ^[n] PA ⊢ prime t₁ ⇒ t ∣ t₁ * t₂ ⇒ t₁ ∣ t ⩒ t ∣ t₂ := by
  pintros 2
  pcontra
  prw [neg_or_iff] at 0
  papply dvd_mul_coprime at 1
  · papply and_right at 0; papplya 0; passumption
  · pcontra
    prw [LO.neg_lt_iff, le_zero_iff_eq_zero] at 0
    papply and_left at 1
    papplya 1
    prw [0]
    pexact dvd_zero
  · papply prime_gt_one at 2
    papply PO.lt_trans
    · pexact zero_lt_succ
    · passumption 2
  · papply coprime_symm
    prw [coprime_prime_iff]
    · papply and_left at 0; passumption
    · passumption

theorem add_mod_iff_of_dvd_right : ↑ᵀ^[n] PA ⊢ t₃ ∣ t₂ ⇒ mod t (t₁ + t₂) t₃ ⇔ mod t t₁ t₃ := by
  papply exists_elim'
  pintros 2; simp
  prw [0, add_mul_mod_iff]
  prefl

theorem add_mod_iff_of_dvd_left : ↑ᵀ^[n] PA ⊢ t₃ ∣ t₂ ⇒ mod t (t₂ + t₁) t₃ ⇔ mod t t₁ t₃ := by
  prw [add_comm]; pexact add_mod_iff_of_dvd_right

theorem exists_seq_le (l p) :
  ↑ᵀ^[n] PA ⊢ ∀[≺ l] ∃' p ⇒ ∃' ∀[≺ ↑ₜl] ∃' (p[#0 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 3)]ₚ ⩑ #0 ⪯ #2) := by
  pintro
  psuffices ∀[≺ S l] ∃' ∀[≺ #1] ∃' (p[#0 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 4)]ₚ ⩑ #0 ⪯ #2)
  · papply forall_elim l at 0; simp [←Formula.subst_comp, Subst.comp_def]
    papplya 0
    pexact lt_succ_self
  papply ind <;> simp [←Formula.subst_comp, Subst.comp_def]
  · pintro
    papply exists_intro 0; pintros 2; simp
    papply not_lt_zero at 0
    papply false_elim
    passumption
  · pintros 3
    prw [succ_lt_succ_iff] at 0
    pspecialize 1 with 1
    · papply lt_succ_of_lt; passumption 0
    prevert 1; papply exists_elim'; pintros 2
    simp [Formula.shift, ←Term.shift_def, ←Formula.subst_comp, Subst.comp_def]; simp_vec
    papply forall_elim #1 at 2; simp [←Formula.subst_comp, Subst.comp_def]
    pspecialize 2 with 1
    · passumption 1
    prevert 2; papply exists_elim'; pintros 2
    simp [Formula.shift, ←Term.shift_def, ←Formula.subst_comp, Subst.comp_def]
    papply or_elim
    · pexact LO.le_total #1 #0
    · pintro
      papply exists_intro #0; simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
      pintro; simp
      prw [lt_succ_iff_lt_or_eq]
      papply or_elim'
      · pintro; papply forall_elim #0 at 3
        simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
        papplya 3 at 0
        prevert; papply exists_elim'; pintro; prw [and_imp_iff]; pintros 2
        papply exists_intro #0
        simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def, Subst.single]
        papply and_intro
        · passumption
        · papply PO.le_trans <;> passumption
      · pintro
        papply exists_intro #1
        simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def, Subst.single]
        papply and_intro
        · prw [0]; passumption
        · pexact PO.le_refl
    · pintro
      papply exists_intro #1; simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
      pintro; simp
      prw [lt_succ_iff_lt_or_eq]
      papply or_elim'
      · pintro; papply forall_elim #0 at 3
        simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
        papplya 3 at 0
        prevert; papply exists_elim'; pintro; prw [and_imp_iff]; pintros 2
        papply exists_intro #0
        simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
        papply and_intro <;> passumption
      · pintro
        papply exists_intro #1
        simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def, Subst.single]
        papply and_intro
        · prw [0]; passumption
        · passumption

theorem exists_seq_dvd (l p) :
  ↑ᵀ^[n] PA ⊢ ∀[≺ l] ∃' (p ⩑ 0 ≺ #0)
    ⇒ ∃' (0 ≺ #0 ⩑ ∀[≺ ↑ₜl] ∃' (p[#0 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 3)]ₚ ⩑ #0 ∣ #2)) := by
  pintro
  psuffices ∀[≺ S l] ∃' (0 ≺ #0 ⩑ ∀[≺ #1] ∃' (p[#0 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 4)]ₚ ⩑ #0 ∣ #2))
  · papply forall_elim l at 0; simp [←Formula.subst_comp, Subst.comp_def]
    papplya 0; pexact lt_succ_self
  · papply ind <;> simp [←Formula.subst_comp, Subst.comp_def]
    · pintro
      papply exists_intro 1; simp [←Formula.subst_comp, Subst.comp_def]
      papply and_intro
      · pexact zero_lt_succ
      · pintros 2; simp; papply not_lt_zero at 0; papply false_elim; passumption
    · pintros 3
      prw [succ_lt_succ_iff] at 0
      pspecialize 1 with 1
      · papply lt_succ_of_lt; passumption 0
      prevert 1; papply exists_elim'; pintro; prw [and_imp_iff]; pintros 2
      simp [Formula.shift, ←Term.shift_def, ←Formula.subst_comp, Subst.comp_def]; simp_vec
      papply forall_elim #1 at 3; simp [←Formula.subst_comp, Subst.comp_def]
      pspecialize 3 with 1
      · passumption 2
      prevert 3; papply exists_elim'; pintro; prw [and_imp_iff]; pintros 2
      simp [Formula.shift, ←Term.shift_def, ←Formula.subst_comp, Subst.comp_def]
      papply exists_intro (#1 * #0); simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
      papply and_intro
      · prw [mul_pos_iff]; papply and_intro <;> passumption
      · pintro; simp [Formula.shift, ←Term.shift_def, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
        prw [lt_succ_iff_lt_or_eq]
        papply or_elim'
        · pintro
          papply forall_elim #0 at 3; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
          papplya 3 at 0
          prevert; papply exists_elim'
          pintro; prw [and_imp_iff]; pintros 2
          papply exists_intro #0
          simp [Formula.shift, ←Term.shift_def, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
          papply and_intro
          · passumption
          · papply dvd_mul_of_dvd_right; passumption
        · pintro
          papply exists_intro #1; simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
          papply and_intro
          · prw [0]; passumption
          · pexact dvd_mul_left

set_option maxHeartbeats 500000

/--
  Chinese remainder theorem formalized in `PA`: if `p(x, i)` and `q(x, i)` uniquely describe two
  sequences of numbers `a₀, ⋯, aₗ₋₁` and `d₀, ⋯, dₗ₋₁` with `aᵢ < dᵢ` for each `i`, and
  `d₀, ⋯, dₗ₋₁` are coprime, then there exists a number `m` such that `m % dᵢ = aᵢ` for each `i`.
  -/
theorem chinese_remainder (l p q) :
  ↑ᵀ^[n] PA ⊢ ∀[≺ l] ∃!' p ⇒ ∀[≺ l] ∃!' q
    ⇒ ∀[≺ l] ∀' ∀' (p[#1 ∷ᵥ #2 ∷ᵥ λ i => #(i.addNat 3)]ₚ ⇒ q[#0 ∷ᵥ #2 ∷ᵥ λ i => #(i.addNat 3)]ₚ ⇒ #1 ≺ #0)
    ⇒ ∀[≺ l] ∀[≺ #0] ∀' ∀' (q[#1 ∷ᵥ #3 ∷ᵥ λ i => #(i.addNat 4)]ₚ ⇒ q[#0 ∷ᵥ #2 ∷ᵥ λ i => #(i.addNat 4)]ₚ ⇒ coprime #1 #0)
    ⇒ ∃' ∀[≺ ↑ₜl] ∃' ∃' (p[#1 ∷ᵥ #2 ∷ᵥ λ i => #(i.addNat 4)]ₚ ⩑ q[#0 ∷ᵥ #2 ∷ᵥ λ i => #(i.addNat 4)]ₚ ⩑ mod #1 #3 #0) := by
  pintros 4
  psuffices ∀[≺ S l] ∃' ∀[≺ #1] ∃' ∃' (p[#1 ∷ᵥ #2 ∷ᵥ λ i => #(i.addNat 5)]ₚ ⩑ q[#0 ∷ᵥ #2 ∷ᵥ λ i => #(i.addNat 5)]ₚ ⩑ mod #1 #3 #0)
  · papply forall_elim l at 0
    simp [←Formula.subst_comp, Subst.comp_def, Subst.lift]
    papplya 0
    pexact lt_succ_self
  · papply ind <;> simp [←Formula.subst_comp, Subst.comp_def, Subst.lift]
    · pintro
      papply exists_intro 0; pintros 2; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift]
      papply not_lt_zero at 0
      papply false_elim
      passumption
    · pintros 3
      prw [succ_lt_succ_iff] at 0
      pspecialize 1 with 1
      · papply lt_succ_of_lt; passumption 0
      prevert 1; papply exists_elim'; pintros 2
      simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]; simp_vec
      papply exists_elim
      · papply exists_min
        papply exists_seq_dvd #1 q[#0 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 4)]ₚ
        pintros 2; simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def]
        papply exists_elim
        · papply forall_elim #0 at 6; papplya 6; simp; papply PO.lt_trans <;> passumption
        pintros 2; simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def]
        papply exists_elim
        · papply forall_elim #1 at 6; papplya 6; simp; papply PO.lt_trans <;> passumption
        pintros 2; simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def]
        papply exists_intro #0; simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
        papply and_intro
        · papply and_left at 0; passumption 0
        · papply forall_elim #2 at 6; simp
          pspecialize 6
          · papply PO.lt_trans <;> passumption
          papply forall_elim #1 at 6
          papply forall_elim #0 at 6
          simp [←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
          papply pos_of_lt
          papplya 6
          · papply and_left at 1; passumption 1
          · papply and_left at 0; passumption 0
      pintro; prw [and_imp_iff, and_imp_iff]; pintros 3
      simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
      papply exists_elim
      · papply forall_elim #2 at 8; papplya 8; simp; passumption 4
      pintros 2
      papply exists_elim
      · papply forall_elim #3 at 8; papplya 8; simp; passumption 5
      pintros 2
      simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
      phave coprime #2 #0
      · pintros; prevert 1; papply exists_elim'; pintros
        papply forall_elim #0 at 5
        simp [Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
        pspecialize 5 with 1
        · prw [0]
          papply lt_mul_left
          · prw [0, mul_pos_iff] at 7; papply and_right at 7; passumption 7
          · papply prime_gt_one; passumption 2
        papplya 5
        papply and_intro
        · prw [0, mul_pos_iff] at 7; papply and_right at 7; passumption 7
        · pintros 2; simp [Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
          papply exists_elim
          · papply forall_elim #0 at 13; simp
            papplya 13; papply PO.lt_trans <;> passumption
          pintros 2; papply exists_intro #0
          simp [Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
          papply and_intro
          · papply and_left at 0; passumption 0
          · phave #0 ∣ #6
            · papply exists_elim
              · papply forall_elim #1 at 8; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
                papplya 8; passumption 1
              pintro; prw [and_imp_iff]; pintros 2
              simp [Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
              phave #0 ≐ #1
              · papply and_right at 2; papply forall_elim #0 at 2; simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
                papplya 2; passumption 1
              prw [←0]; passumption 1
            prw [3] at 0; papply dvd_mul_prime at 0
            · prevert; papply or_elim'
              · pintro
                phave coprime #4 #0
                · papply forall_elim #8 at 13; simp [←Formula.subst_comp, Subst.comp_def]
                  pspecialize 13 with 1
                  · passumption 12
                  papply forall_elim #1 at 13; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
                  pspecialize 13 with 1
                  · passumption 2
                  papply forall_elim #4 at 13
                  papply forall_elim #0 at 13
                  simp [←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
                  papplya 13
                  · papply and_left at 6; passumption 6
                  · papply and_left at 1; passumption 1
                papply forall_elim #3 at 0; simp [Subst.single]
                papply false_elim; papplya 0 <;> passumption
              · pintro; passumption 0
            · passumption 5
      phave coprime #0 #2
      · papply coprime_symm; passumption 0
      phave #1 ≺ #0
      · papply forall_elim #4 at 10; simp
        pspecialize 10 with 1
        · passumption 8
        papply forall_elim #1 at 10
        papply forall_elim #0 at 10
        simp [←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
        papplya 10
        · papply and_left at 3; passumption 3
        · papply and_left at 2; passumption 2
      papply coprime_bezout at 2
      · prevert 2; papply exists_elim'; pintro; papply exists_elim'; pintros 2; simp
        papply coprime_bezout at 2
        · prevert 2; papply exists_elim'; pintro; papply exists_elim'; pintros 2
          papply exists_intro (#7 * #4 * #1 + #5 * #6 * #3)
          pintro
          simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
          prw [lt_succ_iff_lt_or_eq]
          papply or_elim'
          · pintro
            papply exists_elim
            · papply forall_elim #0 at 14; simp [Subst.lift, Subst.single]
              papplya 14; papply PO.lt_trans <;> passumption
            pintros 2
            simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
            papply exists_elim
            · papply forall_elim #1 at 14; simp [Subst.lift, Subst.single]
              papplya 14; papply PO.lt_trans <;> passumption
            pintros 2
            papply exists_intro #1
            papply exists_intro #0
            simp [Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
            papply and_intro
            · papply and_left at 1; passumption 1
            papply and_intro
            · papply and_left at 0; passumption 0
            · phave #0 ∣ #9
              · papply exists_elim
                · papply forall_elim #2 at 9; simp [Subst.lift, Subst.single]
                  papplya 9; passumption 2
                pintros 2
                simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
                phave #0 ≐ #1
                · papply and_right at 1; papply forall_elim #0 at 1
                  simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
                  papplya 1; papply and_left at 0; passumption 0
                prw [←0]; papply and_right at 1; passumption 1
              prw [add_mod_iff_of_dvd_right, mul_assoc, 4, mul_succ, add_mod_iff_of_dvd_left]
              · papply exists_elim
                · papply forall_elim #2 at 12; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
                  papplya 12; passumption 3
                pintro; papply exists_elim'; pintro; prw [and_imp_iff, and_imp_iff]; pintros 3
                simp [Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
                phave #1 ≐ #3
                · papply and_right at 5; papply forall_elim #1 at 5
                  simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
                  papplya 5; passumption 2
                phave #0 ≐ #2
                · papply and_right at 5; papply forall_elim #0 at 5
                  simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
                  papplya 5; passumption 2
                prw [←1, ←0]; passumption 2
              · papply dvd_mul_of_dvd_left; papply dvd_mul_of_dvd_right; passumption 0
              · papply dvd_mul_of_dvd_right; papply dvd_mul_of_dvd_left; passumption 0
          · pintro
            papply exists_intro #6
            papply exists_intro #5
            simp [←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
            papply and_intro
            · prw [0]; papply and_left at 5; passumption 5
            papply and_intro
            · prw [0]; papply and_left at 4; passumption 4
            · prw [add_mod_iff_of_dvd_left, mul_assoc, 2, mul_succ, add_mod_iff_of_dvd_left]
              · papply self_mod_of_lt; passumption 3
              · papply dvd_mul_of_dvd_left; papply dvd_mul_of_dvd_right; pexact dvd_refl
              · papply dvd_mul_of_dvd_right; papply dvd_mul_of_dvd_left; pexact dvd_refl
        · papply pos_of_lt; passumption 1
        · passumption 7
      · passumption 7
      · papply pos_of_lt; passumption 0

/--
  Comprehension theorem for Gödel's beta function: if `p(x, i)` uniquely describes a sequence of
  numbers `a₀, ⋯, aₗ₋₁`, then there exists a number `m` that encodes this sequence, i.e.
  `β(m, i) = aᵢ` for each `i`.
  
  Proof sketch: let `lcm(1, 2, ⋯, l) ∣ A`, `B ≥ max(a₀, ⋯, aₗ₋₁)` and `dᵢ = (i + 1) * A * B + 1`,
  then `d₀, ⋯, dₗ₋₁` are coprime. By Chinese remainder theorem, there exists a `C` such that
  `C % dᵢ = aᵢ`, i.e. `β(⟪C, A * B⟫, i) = aᵢ`.
  -/
theorem beta_comprehension (l p) :
  ↑ᵀ^[n] PA ⊢ ∀[≺ l] ∃!' p ⇒ ∃' ∀[≺ ↑ₜl] ∃' (p[#0 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 3)]ₚ ⩑ beta #0 #2 #1) := by
  pintro
  papply exists_elim
  · papply exists_seq_dvd l (#0 ≐ S #1)
    pintros 2; papply exists_intro (S #0); simp
    papply and_intro
    · prefl
    · pexact zero_lt_succ
  pintros 2
  papply exists_elim
  · papply exists_seq_le ↑ₜl (p[#0 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 3)]ₚ)
    pintros 2
    papply forall_elim #0 at 2; simp
    papplya 2 at 0; 
    papply exists_of_exists_unique at 0
    simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]; simp_vec
    passumption 0
  pintros 2
  papply exists_elim
  · papply chinese_remainder ↑ₜ↑ₜl (p[#0 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 4)]ₚ) (#0 ≐ S (S #1 * #3 * #2))
    · simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def]; simp_vec
      passumption 2
    · pintros 2; papply exists_intro (S (S #0 * #2 * #1)); simp [Subst.lift, Subst.single]
      papply and_intro
      · prefl
      · pintros; passumption
    · pintros 6
      simp [Formula.shift, ←Term.shift_def]; simp [←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]; simp_vec
      prw [0, lt_succ_iff_le]
      papply le_mul_of_le_left
      · prw [mul_pos_iff]; papply and_intro
        · pexact zero_lt_succ
        · papply and_left at 4; passumption 4
      · papply exists_elim
        · papply forall_elim #2 at 5; simp [←Formula.subst_comp, Subst.comp_def]
          papplya 5; passumption 2
        pintro; prw [and_imp_iff]; pintros 2; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift]
        papply exists_elim
        · papply forall_elim #3 at 5; simp [←Term.shift_def]; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
          papplya 5; passumption 4
        pintro; prw [and_imp_iff]; pintros 2; simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def, Subst.lift, ←Term.shift_def]
        phave #0 ≐ #1
        · papply forall_elim #0 at 2; simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
          papplya 2; passumption 1
        phave #3 ≐ #1
        · papply forall_elim #3 at 3; simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
          papplya 3; passumption 6
        prw [0, ←1]
        passumption 2
    · pintros 8; simp
      papply exists_elim
      · passumption 2
      pintros 2; simp
      papply and_right at 6; papply forall_elim #0 at 6; simp [←Term.shift_def]
      pspecialize 6 with 1
      · papply PO.lt_trans'
        · passumption 4
        · prw [←0, add_succ, lt_succ_iff_le]; papply le_add_of_le_right; pexact PO.le_refl
      papply exists_elim
      · passumption 6
      pintro; prw [and_imp_iff]; pintros; simp [Subst.lift, Subst.single]
      prw [6] at 0; prw [7, ←5, ←succ_add, ←4, right_distrib, right_distrib, ←add_succ] at 1
      prw [dvd_add_iff_right, prime_dvd_mul_iff, prime_dvd_mul_iff] at 1
      · prevert 1
        papply or_elim'
        · papply or_elim'
          · pintro; prw [←add_one, dvd_add_iff_left] at 1
            · prw [dvd_one_iff_eq_one] at 1; prw [1] at 2
              papply prime_gt_one at 2; papply PO.lt_irrefl at 2; passumption
            · papply dvd_mul_of_dvd_right
              papply dvd_mul_of_dvd_left
              papply dvd_trans <;> passumption
          · pintro; prw [←add_one, dvd_add_iff_left] at 1
            · prw [dvd_one_iff_eq_one] at 1; prw [1] at 2;
              papply prime_gt_one at 2; papply PO.lt_irrefl at 2; passumption
            · papply dvd_mul_of_dvd_right
              papply dvd_mul_of_dvd_left
              passumption
        · pintro; prw [←add_one, dvd_add_iff_left] at 1
          · prw [dvd_one_iff_eq_one] at 1; prw [1] at 2;
            papply prime_gt_one at 2; papply PO.lt_irrefl at 2; passumption
          · papply dvd_mul_of_dvd_left
            passumption
      · passumption
      · passumption
      · passumption
  pintros 2
  papply exists_elim
  · pexact pair_total #0 (#2 * #1)
  pintros 2
  papply exists_intro #0; simp
  pintros 2
  papply forall_elim #0 at 5
  simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]; simp_vec
  pspecialize 5 with 1
  · passumption 0
  papply exists_elim
  · passumption 5
  pintros 2
  papply exists_intro #0
  simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
  papply and_intro
  · papply and_left at 0; passumption 0
  · papply forall_elim #1 at 3
    simp [Term.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
    pspecialize 3 with 1
    · passumption 1
    papply exists_elim
    · passumption 3
    pintro; papply exists_elim'; pintro; prw [and_imp_iff, and_imp_iff]; pintros 3
    simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
    phave #1 ≐ #2
    · papply and_right at 3; papply forall_elim #1 at 3
      simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
      papplya 3; passumption 2
    prw [0, 2] at 1
    papply exists_intro #5; simp [Subst.lift, Subst.single]
    papply and_intro
    · prw [lt_succ_iff_le]; papply left_le_pair; passumption 6
    papply exists_intro (#7 * #6); simp [Subst.single]
    papply and_intro
    · prw [lt_succ_iff_le]; papply right_le_pair; passumption 6
    papply and_intro
    · passumption 6
    · prw [←mul_assoc]; passumption 1

/-- With minimization, the description formula `p` in `beta_comprehension` does not have to be unique. -/
theorem beta_comprehension' (l p) :
  ↑ᵀ^[n] PA ⊢ ∀[≺ l] ∃' p ⇒ ∃' ∀[≺ ↑ₜl] ∃' (p[#0 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 3)]ₚ ⩑ beta #0 #2 #1) := by
  pintro
  papply exists_elim
  · papply beta_comprehension l (p ⩑ ∀[≺ #0] (~ p[#0 ∷ᵥ λ i => #(i.addNat 2)]ₚ))
    pintros 2
    papply forall_elim #0 at 1; simp
    pspecialize 1 with 1
    · passumption 0
    papply exists_min at 1
    papply exists_elim
    · passumption 1
    pintro; prw [and_imp_iff]; pintros 2
    papply exists_intro #0
    simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]; simp_vec
    papply and_intro
    · papply and_intro
      · passumption 1
      · passumption 0
    · pintro; prw [and_imp_iff]; pintros 2
      simp [Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
      pcontra
      prw [LO.ne_iff_lt_or_gt] at 0
      papply or_elim
      · passumption 0
      · pintro
        papply forall_elim #0 at 4
        simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
        papplya 4 <;> passumption
      · pintro
        papply forall_elim #1 at 2
        simp [←Formula.subst_comp, Subst.comp_def, Subst.single]
        papplya 2 <;> passumption
  pintros 2
  papply exists_intro #0
  pintros 2
  papply forall_elim #0 at 1
  simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift]; simp_vec
  pspecialize 1 with 1
  · passumption 0
  papply exists_elim
  · passumption 1
  pintro; prw [and_imp_iff, and_imp_iff]; pintros 3
  papply exists_intro #0
  simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
  papply and_intro <;> passumption

end FirstOrder.Language.Theory.PA
