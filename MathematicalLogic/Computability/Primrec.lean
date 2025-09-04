import Mathlib.Data.Nat.Bits
import Mathlib.Logic.Encodable.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import MathematicalLogic.Vec

@[simp] theorem ite_pos_iff [Decidable p] : 0 < (if p then 1 else 0) ↔ p := by
  by_cases h : p <;> simp [h]

@[simp] theorem ite_zero_iff [Decidable p] : 0 = (if p then 1 else 0) ↔ ¬ p := by
  by_cases h : p <;> simp [h]

@[simp] protected theorem Nat.mul_pos_iff {a b : ℕ} : 0 < a * b ↔ 0 < a ∧ 0 < b := by
  constructor
  · intro h; exact ⟨Nat.pos_of_mul_pos_right h, Nat.pos_of_mul_pos_left h⟩
  · intro ⟨h₁, h₂⟩; exact Nat.mul_pos h₁ h₂

inductive Primrec : ℕ → Type where
| const : ℕ → Primrec n
| succ : Primrec 1
| proj : Fin n → Primrec n
| comp : Primrec n → (Fin n → Primrec m) → Primrec m
| prec : Primrec n → Primrec (n + 2) → Primrec (n + 1)

namespace Primrec

abbrev comp₀ (f : Primrec 0) : Primrec n := f.comp []ᵥ
abbrev comp₁ (f : Primrec 1) (g : Primrec n) := f.comp [g]ᵥ
abbrev comp₂ (f : Primrec 2) (g₁ g₂ : Primrec n) := f.comp [g₁, g₂]ᵥ
abbrev comp₃ (f : Primrec 3) (g₁ g₂ g₃ : Primrec n) := f.comp [g₁, g₂, g₃]ᵥ
abbrev comp₄ (f : Primrec 4) (g₁ g₂ g₃ g₄ : Primrec n) := f.comp [g₁, g₂, g₃, g₄]ᵥ
abbrev comp₅ (f : Primrec 5) (g₁ g₂ g₃ g₄ g₅ : Primrec n) := f.comp [g₁, g₂, g₃, g₄, g₅]ᵥ
abbrev comp₆ (f : Primrec 6) (g₁ g₂ g₃ g₄ g₅ g₆ : Primrec n) := f.comp [g₁, g₂, g₃, g₄, g₅, g₆]ᵥ
abbrev zero : Primrec n := const 0

def eval : Primrec n → Vec ℕ n → ℕ
| const n, _ => n
| succ, v => v.head.succ
| proj i, v => v i
| comp f g, v => f.eval (λ i => (g i).eval v)
| prec f g, v => v.head.recOn (f.eval v.tail) (λ n ih => g.eval (n ∷ᵥ ih ∷ᵥ v.tail))
instance : CoeFun (Primrec n) (λ _ => Vec ℕ n → ℕ) := ⟨eval⟩

@[simp] theorem const_eval : const n v = n := rfl
@[simp] theorem succ_eval : succ v = v.head.succ := rfl
@[simp] theorem proj_eval : proj i v = v i := rfl
@[simp low] theorem comp_eval : comp f g v = f (λ i => g i v) := rfl
@[simp] theorem comp₀_eval : comp₀ f v = f []ᵥ := by simp [Vec.eq_nil]
@[simp] theorem comp₁_eval : comp₁ f g v = f [g v]ᵥ := by simp [Vec.eq_one]
@[simp] theorem comp₂_eval : comp₂ f g₁ g₂ v = f [g₁ v, g₂ v]ᵥ := by simp [Vec.eq_two]
@[simp] theorem comp₃_eval : comp₃ f g₁ g₂ g₃ v = f [g₁ v, g₂ v, g₃ v]ᵥ := by simp [Vec.eq_three]
@[simp] theorem comp₄_eval : comp₄ f g₁ g₂ g₃ g₄ v = f [g₁ v, g₂ v, g₃ v, g₄ v]ᵥ := by simp [Vec.eq_four]

theorem prec_eval : prec f g v = v.head.recOn (f.eval v.tail) λ n ih => g.eval (n ∷ᵥ ih ∷ᵥ v.tail) := rfl
theorem prec_eval_zero : prec f g (0 ∷ᵥ v) = f.eval v := rfl
theorem prec_eval_succ : prec f g ((n + 1) ∷ᵥ v) = g.eval (n ∷ᵥ prec f g (n ∷ᵥ v) ∷ᵥ v) := rfl

attribute [local simp] Vec.head Vec.tail Function.comp_def

def id : Primrec 1 :=
  proj 0
@[simp] theorem id_eval : id v = v 0 := by
  simp [id]

def swap (f : Primrec (n + 2)) : Primrec (n + 2) :=
  f.comp (proj 1 ∷ᵥ proj 0 ∷ᵥ (proj ·.succ.succ))
@[simp] theorem swap_eval : swap f v = f (v 1 ∷ᵥ v 0 ∷ᵥ v.tail.tail) := by
  simp [swap]; congr; ext i
  cases i using Fin.cases with simp
  | succ i => cases i using Fin.cases <;> simp

def cases (f : Primrec n) (g : Primrec (n + 1)) : Primrec (n + 1) :=
  f.prec (g.comp (proj 0 ∷ᵥ (proj ·.succ.succ)))
theorem cases_eval : cases f g v = v.head.casesOn (f v.tail) λ n => g (n ∷ᵥ v.tail) := by
  rw [Vec.eq_cons v]
  generalize v.head = n
  cases n with
  | zero => rfl
  | succ => simp [cases, prec_eval_succ]; simp_vec
theorem cases_eval_zero : cases f g (0 ∷ᵥ v) = f.eval v := rfl
theorem cases_eval_succ : cases f g ((n + 1) ∷ᵥ v) = g.eval (n ∷ᵥ v) := by
  simp [cases, prec_eval_succ]; simp_vec

def add : Primrec 2 :=
  (proj 0).prec (succ.comp₁ (proj 1))
@[simp] theorem add_eval : add v = v 0 + v 1 := by
  simp [add, prec_eval]
  generalize v 0 = n, v 1 = m
  induction n generalizing m with simp
  | succ n ih => simp [ih, Nat.succ_add]

def mul : Primrec 2 :=
  zero.prec (add.comp₂ (proj 1) (proj 2))
@[simp] theorem mul_eval : mul v = v 0 * v 1 := by
  simp [mul, prec_eval]
  generalize v 0 = n, v 1 = m
  induction n generalizing m with simp
  | succ n ih => simp [ih, Nat.succ_mul]

def exp : Primrec 2 :=
  ((const 1).prec (mul.comp₂ (proj 1) (proj 2))).swap
@[simp] theorem exp_eval : exp v = v 0 ^ v 1 := by
  simp [exp, prec_eval]
  generalize v 0 = n, v 1 = m
  induction m generalizing n with simp
  | succ m ih => simp [ih]; rfl

def pred : Primrec 1 :=
  zero.prec (proj 0)
@[simp] theorem pred_eval : pred v = (v 0).pred := by
  simp [pred, prec_eval]
  generalize v 0 = n
  cases n <;> simp

def sub : Primrec 2 :=
  ((proj 0).prec (pred.comp₁ (proj 1))).swap
@[simp] theorem sub_eval : sub v = v 0 - v 1 := by
  simp [sub, prec_eval]
  generalize v 0 = n, v 1 = m
  induction m generalizing n with simp
  | succ m ih => simp [ih]; rfl

def sign : Primrec 1 :=
  zero.cases (const 1)
@[simp] theorem sign_eval : sign v = if 0 < v 0 then 1 else 0 := by
  simp [sign, cases_eval]
  generalize v 0 = n
  cases n <;> simp

def nsign : Primrec 1 :=
  (const 1).cases (const 0)
@[simp] theorem nsign_eval : nsign v = if v 0 = 0 then 1 else 0 := by
  simp [nsign, cases_eval]
  generalize v 0 = n
  cases n <;> simp

def not (f : Primrec n) := nsign.comp₁ f
@[simp] theorem not_eval_pos_iff : 0 < not f v ↔ f v = 0 := by simp [not]
@[simp] theorem not_eval_zero_iff : not f v = 0 ↔ 0 < f v := by simp [not, pos_iff_ne_zero]

def and (f g : Primrec n) := mul.comp₂ f g
@[simp] theorem and_eval_pos_iff : 0 < and f g v ↔ 0 < f v ∧ 0 < g v := by simp [and]
@[simp] theorem and_eval_zero_iff : and f g v = 0 ↔ f v = 0 ∨ g v = 0 := by simp [and]

def andv (f : Vec (Primrec n) m) : Primrec n :=
  match m with
  | 0 => const 1
  | _ + 1 => and f.head (andv f.tail)
@[simp] theorem andv_eval_pos_iff {f : Vec (Primrec n) m} : 0 < andv f v ↔ ∀ i, 0 < f i v := by
  induction m with simp [andv]
  | succ m ih => simp [ih, Fin.forall_fin_succ]
@[simp] theorem andv_eval_zero_iff {f : Vec (Primrec n) m} : andv f v = 0 ↔ ∃ i, f i v = 0 := by
  rw [←not_iff_not, ←ne_eq]; simp [←pos_iff_ne_zero]

def or (f g : Primrec n) := add.comp₂ f g
@[simp] theorem or_eval_pos_iff : 0 < or f g v ↔ 0 < f v ∨ 0 < g v := by simp [or]
@[simp] theorem or_eval_zero_iff : or f g v = 0 ↔ f v = 0 ∧ g v = 0 := by simp [or]

def orv (f : Vec (Primrec n) m) : Primrec n :=
  match m with
  | 0 => const 0
  | _ + 1 => or f.head (orv f.tail)
@[simp] theorem orv_eval_pos_iff {f : Vec (Primrec n) m} : 0 < orv f v ↔ ∃ i, 0 < f i v := by
  induction m with simp [orv]
  | succ m ih => simp [ih, Fin.exists_fin_succ]
@[simp] theorem orv_eval_zero_iff {f : Vec (Primrec n) m} : orv f v = 0 ↔ ∀ i, f i v = 0 := by
  rw [←not_iff_not, ←ne_eq]; simp [←pos_iff_ne_zero]

def lt (f g : Primrec n) := sub.comp₂ g f
@[simp] theorem lt_eval_pos_iff : 0 < lt f g v ↔ f v < g v := by
  simp [lt]
@[simp] theorem lt_eval_zero_iff : lt f g v = 0 ↔ g v ≤ f v := by
  simp [lt, Nat.sub_eq_zero_iff_le]

abbrev gt (f g : Primrec n) := lt g f

def le (f g : Primrec n) := nsign.comp₁ (lt g f)
@[simp] theorem le_eval_pos_iff : 0 < le f g v ↔ f v ≤ g v := by
  simp [le]
@[simp] theorem le_eval_zero_iff : le f g v = 0 ↔ g v < f v := by
  simp [le]

abbrev ge (f g : Primrec n) := le g f

def eq (f g : Primrec n) := and (le f g) (ge f g)
@[simp] theorem eq_eval_pos_iff : 0 < eq f g v ↔ f v = g v := by
  simp [eq, Nat.eq_iff_le_and_ge]
@[simp] theorem eq_eval_zero_iff : eq f g v = 0 ↔ f v ≠ g v := by
  simp [eq, ne_comm]

abbrev ne (f g : Primrec n) := not (eq f g)

def cond : Primrec 3 :=
  (proj 1).cases (proj 1)
@[simp] theorem cond_eval : cond v = if 0 < v 0 then v 1 else v 2 := by
  simp [cond, cases_eval]
  cases v 0 <;> simp

def ite (f g h : Primrec n) : Primrec n :=
  cond.comp₃ f g h
@[simp] theorem ite_eval : ite f g h v = if 0 < f v then g v else h v := by
  simp [ite]

def odd : Primrec 1 :=
  zero.prec (nsign.comp₁ (proj 1))
@[simp] theorem odd_eval : odd v = if (v 0).bodd then 1 else 0 := by
  simp [odd, prec_eval]
  generalize v 0 = n
  induction n with simp
  | succ n ih => simp [ih]

def div2 : Primrec 1 :=
  zero.prec (ite (odd.comp₁ (proj 0)) (succ.comp₁ (proj 1)) (proj 1))
@[simp] theorem div2_eval : div2 v = (v 0).div2 := by
  simp [div2, prec_eval]
  generalize v 0 = n
  induction n with simp
  | succ n ih => simp [ih]

def mod : Primrec 2 :=
  ite (proj 1) (zero.prec (ite (lt (succ.comp₁ (proj 1)) (proj 2)) (succ.comp₁ (proj 1)) zero)) (proj 0)
@[simp] theorem mod_eval : mod v = v 0 % v 1 := by
  simp [mod, prec_eval]
  generalize v 0 = n, v 1 = m
  by_cases h₁ : 0 < m
  · simp [h₁]
    induction n with simp
    | succ n ih =>
      simp [ih]
      split
      next h₂ =>
        rw [Nat.add_mod_eq_ite]
        simp [Nat.mod_eq_of_lt ((Nat.le_add_left _ _).trans_lt h₂), not_le_of_gt h₂]
      next h₂ =>
        simp at h₂
        apply eq_of_le_of_ge (Nat.mod_lt _ h₁) at h₂
        rw [←Nat.div_add_mod n m, add_assoc, h₂]
        simp
  · simp at h₁; simp [h₁]

def max : Primrec 2 :=
  ite (le (proj 0) (proj 1)) (proj 1) (proj 0)
@[simp] theorem max_eval : max v = (v 0).max (v 1) := by
  simp [max, Nat.max_def]

def pair : Primrec 2 :=
  ite
    (gt (proj 1) (proj 0))
    (add.comp₂ (mul.comp₂ (proj 1) (proj 1)) (proj 0))
    (add.comp₂ (mul.comp₂ (proj 0) (succ.comp₁ (proj 0))) (proj 1))
@[simp] theorem pair_eval : pair v = (v 0).pair (v 1) := by
  simp [pair, Nat.pair, Nat.mul_succ]

def sqrt : Primrec 1 :=
  zero.prec 
    (ite
      (eq
        (mul.comp₂ (succ.comp₁ (proj 1)) (succ.comp₁ (proj 1)))
        (succ.comp₁ (proj 0)))
      (succ.comp₁ (proj 1))
      (proj 1))
@[simp] theorem sqrt_eval : sqrt v = (v 0).sqrt := by
  simp [sqrt, prec_eval]
  generalize v 0 = n
  induction n with simp
  | succ n ih =>
    simp [ih]
    by_cases h : (n.sqrt + 1) * (n.sqrt + 1) = n + 1 <;> simp [h]
    · conv => rhs; rw [←h]
      rw [Nat.sqrt_eq]
    · rw [Nat.eq_sqrt]
      constructor
      · apply Nat.le_succ_of_le
        apply Nat.sqrt_le
      · apply Nat.lt_of_le_of_ne
        · apply Nat.lt_succ_sqrt
        · exact Ne.symm h

def fst : Primrec 1 :=
  ite
    (gt
      (sqrt.comp₁ (proj 0))
      (sub.comp₂ (proj 0) (mul.comp₂ (sqrt.comp₁ (proj 0)) (sqrt.comp₁ (proj 0)))))
    (sub.comp₂ (proj 0) (mul.comp₂ (sqrt.comp₁ (proj 0)) (sqrt.comp₁ (proj 0))))
    (sqrt.comp₁ (proj 0))
@[simp] theorem fst_eval : fst v = (v 0).unpair.1 := by
  simp [fst, Nat.unpair]
  split <;> simp

def snd : Primrec 1 :=
  ite
    (gt
      (sqrt.comp₁ (proj 0))
      (sub.comp₂ (proj 0) (mul.comp₂ (sqrt.comp₁ (proj 0)) (sqrt.comp₁ (proj 0)))))
    (sqrt.comp₁ (proj 0))
    (sub.comp₂ (proj 0) (mul.comp₂ (sqrt.comp₁ (proj 0)) (succ.comp₁ (sqrt.comp₁ (proj 0)))))
@[simp] theorem snd_eval : snd v = (v 0).unpair.2 := by
  simp [snd, Nat.unpair, Nat.mul_succ, Nat.sub_add_eq]
  split <;> simp

def paired (f : Primrec (n + 1)) : Primrec (n + 2) :=
  f.comp (pair.comp₂ (proj 0) (proj 1) ∷ᵥ (proj ·.succ.succ))
@[simp] theorem paired_eval : paired f v = f ((v 0).pair (v 1) ∷ᵥ v.tail.tail) := by
  simp [paired]; congr; ext i; cases i using Fin.cases <;> simp

def unpaired (f : Primrec (n + 2)) : Primrec (n + 1) :=
  f.comp (fst.comp₁ (proj 0) ∷ᵥ snd.comp₁ (proj 0) ∷ᵥ (proj ·.succ))
@[simp] theorem unpaired_eval : unpaired f v = f ((v 0).unpair.1 ∷ᵥ (v 0).unpair.2 ∷ᵥ v.tail) := by
  simp [unpaired]; congr; ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => cases i using Fin.cases <;> simp

def iterate (f : Primrec (n + 1)) : Primrec (n + 2) :=
  (proj 0).prec (f.comp (proj 1 ∷ᵥ (proj ·.succ.succ.succ)))
theorem iterate_eval : iterate f (n ∷ᵥ x ∷ᵥ v) = (λ x => f (x ∷ᵥ v))^[n] x := by
  simp [iterate]
  induction n with
  | zero => simp [prec_eval_zero]
  | succ n ih => rw [Function.iterate_succ']; simp [prec_eval_succ, ih]; simp_vec

def vget : Primrec 2 :=
  fst.comp₁ (iterate snd).swap
theorem vget_eval {v : Vec ℕ n} {i : Fin n} :
  vget [v.paired, i]ᵥ = v i := by
  simp [vget, iterate_eval]
  induction n with simp [Vec.paired]
  | zero => exact i.elim0
  | succ n ih => cases i using Fin.cases <;> simp [ih]
theorem vget_eval' {v : Vec ℕ n} (h : i < n) :
  vget [v.paired, i]ᵥ = v ⟨i, h⟩ :=
  vget_eval (i := ⟨i, h⟩)

def isvec : Primrec 2 :=
  not (iterate snd)
theorem isvec_eval_pos_iff : 0 < isvec [n, k]ᵥ ↔ ∃ (v : Vec ℕ n), k = v.paired := by
  simp [isvec, iterate_eval]
  induction n generalizing k with simp [Vec.paired]
  | succ n ih =>
    simp [ih]
    constructor
    · intro ⟨v, h⟩; exists k.unpair.1 ∷ᵥ v; simp [←h]
    · intro ⟨v, h⟩; exists v.tail; simp [h]

def vmk (f : Primrec (n + 1)) : Primrec (n + 1) :=
  (zero.prec
    (pair.comp₂ (f.comp ((pred.comp₁ (sub.comp₂ (proj 2) (proj 0))) ∷ᵥ (proj ·.succ.succ.succ))) (proj 1))
    ).comp (proj 0 ∷ᵥ proj 0 ∷ᵥ (proj ·.succ))
theorem vmk_eval : vmk f (n ∷ᵥ v) = Vec.paired λ (i : Fin n) => f (i ∷ᵥ v) := by
  simp [vmk]
  generalize h : prec _ _ = g
  suffices h' : ∀ m ≤ n, g (m ∷ᵥ n ∷ᵥ v) = Vec.paired λ (i : Fin m) => f ((i + n - m) ∷ᵥ v) by
    simp_vec; rw [h'] <;> simp
  subst h; intro m h; simp [prec_eval]
  induction m with simp [Vec.paired]
  | succ m ih =>
    constructor
    · simp_vec; rfl
    · rw [ih]
      · congr; ext; rw [Nat.succ_add, Nat.succ_sub_succ]
      · exact Nat.le_of_succ_le h

def vmap (f : Primrec (n + 1)) : Primrec (n + 2) :=
  vmk (f.comp (vget.comp₂ (proj 1) (proj 0) ∷ᵥ (proj ·.succ.succ)))
theorem vmap_eval {v : Vec ℕ n} : vmap f (n ∷ᵥ v.paired ∷ᵥ w) = Vec.paired λ i => f (v i ∷ᵥ w) := by
  simp [vmap]
  rw [vmk_eval]
  congr; ext i
  simp; simp_vec
  rw [vget_eval]

def rcons : Primrec 3 :=
  ((pair.comp₂ (proj 2) zero).prec
    (pair.comp₂
      (vget.comp₂ (proj 3) (sub.comp₂ (proj 2) (succ.comp₁ (proj 0))))
      (proj 1))).comp₄ (proj 0) (proj 0) (proj 1) (proj 2)
theorem rcons_eval {v : Vec ℕ n} :
  rcons [n, v.paired, x]ᵥ = (v.rcons x).paired := by
  simp [rcons]
  generalize h : prec _ _ = f
  suffices h' : ∀ k (h : k ≤ n), f [k, n, v.paired, x]ᵥ =
    (Vec.rcons (λ j : Fin k =>
      v ⟨j + (n - k), by apply Nat.add_lt_of_lt_sub; simp [Nat.sub_sub_self h]⟩) x).paired by
    simp [Vec.eq_four]; simp; rw [h'] <;> simp
  subst h; intro k h; simp [prec_eval, Vec.eq_two]; simp
  induction k with simp
  | zero => simp [Vec.eq_nil, Vec.paired]
  | succ k ih =>
    simp_vec
    conv => rhs; simp [Vec.paired]
    congr
    · rw [←vget_eval (v := v)]
    · rw [ih (Nat.le_of_succ_le h)]
      congr 1; funext i
      simp [Vec.rcons, Fin.snoc]
      by_cases h' : (i : ℕ) < k <;> simp [h']
      simp_rw [Nat.succ_add, ←Nat.add_succ, ←Nat.succ_sub h, Nat.succ_sub_succ]

def cov (f : Primrec (n + 2)) : Primrec (n + 1) :=
  zero.prec (rcons.comp₃ (proj 0) (proj 1) f)
theorem cov_eval {f : Primrec (n + 2)} :
  f.cov (m ∷ᵥ v) = Vec.paired (λ i : Fin m => f (i ∷ᵥ f.cov (i ∷ᵥ v) ∷ᵥ v)) := by
  induction m with
  | zero => simp [Vec.paired, cov, prec_eval]
  | succ m ih =>
    conv =>
      lhs; rw [cov, prec_eval_succ, ←cov]
      simp [Vec.eq_three]; simp
      rw [ih]
      simp [rcons_eval]
    congr! with i
    cases i using Fin.lastCases <;> simp [ih]

def covrec (f : Primrec (n + 2)) : Primrec (n + 1) :=
  vget.comp₂ (f.cov.comp (succ.comp₁ (proj 0) ∷ᵥ (proj ·.succ))) (proj 0)
theorem covrec_eval {f : Primrec (n + 2)} :
  f.covrec (m ∷ᵥ v) = f (m ∷ᵥ Vec.paired (λ i : Fin m => f.covrec (i ∷ᵥ v)) ∷ᵥ v) := by
  simp [covrec, Vec.eq_two]; simp_vec
  rw [cov_eval, vget_eval' (Nat.lt_succ_self _)]
  congr!; rw [cov_eval]
  congr; funext i; simp_vec
  conv => rhs; rw [cov_eval]
  simp [vget_eval']

def div : Primrec 2 :=
  ite (not (proj 1)) zero
    (covrec (ite (lt (proj 0) (proj 2)) zero (succ.comp₁ (vget.comp₂ (proj 1) (sub.comp₂ (proj 0) (proj 2))))))
@[simp] theorem div_eval : div v = v 0 / v 1 := by
  simp [div]
  rw [Vec.eq_two v]; generalize v 0 = n, v 1 = m; simp
  by_cases h₁ : m = 0 <;> simp [h₁]
  simp [Nat.ne_zero_iff_zero_lt] at h₁
  induction' n using Nat.strong_induction_on with n ih
  rw [covrec_eval]; simp
  by_cases h₃ : n < m
  · simp [eq_comm, Nat.div_eq_zero_iff, h₃]
  · simp at h₃
    have h₄ : n - m < n := Nat.sub_lt (h₁.trans_le h₃) h₁
    rw [vget_eval' h₄, ih _ h₄]
    simp [not_lt_of_ge h₃]
    conv => rhs; rw [Nat.div_eq]; simp [h₁, h₃]

def vmap' : Primrec 3 :=
  paired (covrec (unpaired 
    (ite (not (proj 0)) zero
      (pair.comp₂ (vget.comp₂ (proj 3) (fst.comp₁ (proj 1)))
        (vget.comp₂ (proj 2) (pair.comp₂ (pred.comp₁ (proj 0)) (snd.comp₁ (proj 1))))))))
theorem vmap'_eval {v : Vec ℕ n} {f : Vec ℕ m} (h : ∀ i, v i < m) :
  vmap' [n, v.paired, f.paired]ᵥ = Vec.paired λ i => f ⟨v i, h i⟩ := by
  simp [vmap']
  induction' n using Nat.strong_induction_on with n ih
  rw [covrec_eval]; simp
  cases n with simp [Vec.paired]
  | succ n =>
    simp [Vec.eq_two]; simp
    rw [vget_eval' (h 0)]; simp
    rw [vget_eval']
    · apply ih; simp
    · apply Nat.pair_lt_pair_left'
      · simp
      · apply Nat.right_le_pair

def vmax : Primrec 2 :=
  paired (covrec (unpaired
    (ite (not (proj 0)) zero
      (max.comp₂ (fst.comp₁ (proj 1)) (vget.comp₂ (proj 2) (pair.comp₂ (pred.comp₁ (proj 0)) (snd.comp₁ (proj 1))))))))
theorem vmax_eval {v : Vec ℕ n} : vmax [n, v.paired]ᵥ = v.max := by
  simp [vmax]
  induction' n using Nat.strong_induction_on with n ih
  rw [covrec_eval]; simp
  cases n with simp [Vec.paired, Vec.max]
  | succ n =>
    rw [vget_eval']
    · congr; apply ih; simp
    · apply Nat.pair_lt_pair_left'
      · simp
      · apply Nat.right_le_pair

def vand : Primrec 2 :=
  not (vmax.comp₂ (proj 0) ((vmap nsign).comp₂ (proj 0) (proj 1)))
theorem vand_eval_pos_iff {v : Vec ℕ n} : 0 < vand [n, v.paired]ᵥ ↔ ∀ i, v i > 0 := by
  simp [vand, Vec.eq_two]; simp [vmap_eval, vmax_eval, Vec.max_zero_iff, Nat.ne_zero_iff_zero_lt]



def bdMu (f : Primrec (n + 1)) : Primrec (n + 1) :=
  zero.prec (ite (lt (proj 1) (proj 0)) (proj 1)
    (ite (f.comp (proj 0 ∷ᵥ (proj ·.succ.succ)))
      (proj 0) (succ.comp₁ (proj 0))))

theorem bdMu_eval_le_self :
  bdMu f (m ∷ᵥ v) ≤ m := by
  induction m with
  | zero => simp [bdMu, prec_eval_zero]
  | succ m ih =>
    rw [bdMu, prec_eval_succ, ←bdMu]; simp
    split
    · exact Nat.le_succ_of_le ih
    · split <;> simp

lemma bdMu_eval_gt :
  k < bdMu f (m ∷ᵥ v) → f (k ∷ᵥ v) = 0 := by
  intro h
  induction m with
  | zero => simp [bdMu, prec_eval_zero] at h
  | succ m ih =>
    rw [bdMu, prec_eval_succ, ←bdMu] at h; simp at h
    split at h
    next => exact ih h
    next h₁ =>
      simp at h₁; simp_vec at h
      split at h
      next => exact ih (Nat.lt_of_lt_of_le h h₁)
      next h₂ =>
        simp at h₂
        simp [Nat.lt_succ_iff_lt_or_eq] at h
        rcases h with h | h
        · exact ih (Nat.lt_of_lt_of_le h h₁)
        · rw [h]; exact h₂

theorem bdMu_eval_lt_self :
  bdMu f (m ∷ᵥ v) < m → f (bdMu f (m ∷ᵥ v) ∷ᵥ v) > 0 := by
  intro h
  induction m with
  | zero => simp [bdMu] at h
  | succ m ih =>
    rw [bdMu, prec_eval_succ, ←bdMu] at *; simp at *
    split at h
    next h₁ => simp [h₁]; exact ih h₁
    next h₁ =>
      simp [h₁]; simp_vec at *
      split at h <;> simp at h
      next h₂ => simp [h₂]

theorem bdMu_eval_lt_self_iff :
  bdMu f (m ∷ᵥ v) < m ↔ ∃ k < m, f (k ∷ᵥ v) > 0 := by
  constructor
  · intro h; exists _, h
    exact bdMu_eval_lt_self h
  · intro ⟨k, h₁, h₂⟩
    by_contra h₃
    simp at h₃
    apply Nat.ne_of_gt h₂
    apply bdMu_eval_gt
    exact Nat.lt_of_lt_of_le h₁ h₃

theorem bdMu_eval_eq {f : Primrec _} :
  n ≤ m → (∀ k < n, f (k ∷ᵥ v) = 0) → f (n ∷ᵥ v) > 0 → bdMu f (m ∷ᵥ v) = n := by
  intro h₁ h₂ h₃
  by_contra h; apply lt_or_gt_of_ne at h; rcases h with h | h
  · have := lt_of_lt_of_le h h₁
    apply bdMu_eval_lt_self at this
    simp [h₂ _ h] at this
  · apply bdMu_eval_gt at h
    simp [h] at h₃

def bdExists (f : Primrec n) (g : Primrec (n + 1)) : Primrec n :=
  lt ((bdMu g).comp (f ∷ᵥ proj)) f
@[simp] theorem bdExists_eval_pos_iff :
  0 < bdExists f g v ↔ ∃ k < f v, 0 < g (k ∷ᵥ v) := by
  simp [bdExists]; simp_vec; exact bdMu_eval_lt_self_iff
@[simp] theorem bdExists_eval_zero_iff :
  bdExists f g v = 0 ↔ ∀ k < f v, g (k ∷ᵥ v) = 0 := by
  rw [←not_iff_not]
  simp [Nat.ne_zero_iff_zero_lt]

def bdForall (f : Primrec n) (g : Primrec (n + 1)) : Primrec n :=
  not (bdExists f (not g))
@[simp] theorem bdForall_eval_pos_iff :
  0 < bdForall f g v ↔ ∀ k < f v, 0 < g (k ∷ᵥ v) := by
  simp [bdForall, bdExists_eval_zero_iff]
@[simp] theorem bdForall_eval_zero_iff :
  bdForall f g v = 0 ↔ ∃ k < f v, g (k ∷ᵥ v) = 0 := by
  rw [←not_iff_not]
  simp [Nat.ne_zero_iff_zero_lt]

open Lean.Parser Std in
def repr : Primrec n → ℕ → Format
| const n, _ => "const " ++ n.repr
| succ, _ => "succ"
| proj i, p => Repr.addAppParen ("proj " ++ reprPrec i maxPrec) p
| comp f v, p => Repr.addAppParen ("comp " ++ repr f maxPrec ++ " " ++ Format.bracketFill "[" (Format.joinSep (Vec.toList λ i => (v i).repr 0) ", ") "]ᵥ") p
| prec f g, p => Repr.addAppParen ("prec " ++ repr f maxPrec ++ " " ++ repr g maxPrec) p

instance : Repr (Primrec n) := ⟨repr⟩

end Primrec
