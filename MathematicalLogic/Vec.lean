import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Encodable.Basic

/-!

# Vector

This files defines `Vec` as an abbreviation of `Fin n → α`. (This is different with `Vector`.)
A lot of definitions in this file are just encapsulations of those under `Fin` namespace; the reason
to create a new namespace is to allow dot notation and to avoid potential naming collision.

`Vec` type is heavily used in this library, mainly because `(Fin n → α) → α` can be used in inductive
definitions very naturally (while other solutions, including `List α → α` and `mutual inductive`,
generate very complicated recursors).

-/

namespace Nat

lemma pair_le_pair_left (h : a₁ ≤ a₂) : pair a₁ b ≤ pair a₂ b := by
  cases lt_or_eq_of_le h with
  | inl h => apply le_of_lt; apply pair_lt_pair_left; exact h
  | inr h => rw [h]
lemma pair_le_pair_right (h : b₁ ≤ b₂) : pair a b₁ ≤ pair a b₂ := by
  cases lt_or_eq_of_le h with
  | inl h => apply le_of_lt; apply pair_lt_pair_right; exact h
  | inr h => rw [h]
lemma pair_lt_pair_left' (h₁ : a₁ < a₂) (h₂ : b₁ ≤ b₂) : pair a₁ b₁ < pair a₂ b₂ :=
  lt_of_lt_of_le (pair_lt_pair_left _ h₁) (pair_le_pair_right h₂)
lemma pair_lt_pair_right' (h₁ : a₁ ≤ a₂) (h₂ : b₁ < b₂) : pair a₁ b₁ < pair a₂ b₂ :=
  lt_of_le_of_lt (pair_le_pair_left h₁) (pair_lt_pair_right _ h₂)
lemma pair_le_pair (h₁ : a₁ ≤ a₂) (h₂ : b₁ ≤ b₂) : pair a₁ b₁ ≤ pair a₂ b₂ :=
  le_trans (pair_le_pair_left h₁) (pair_le_pair_right h₂)

end Nat

namespace Fin

@[simp] theorem succ_two_eq_three : Fin.succ (2 : Fin (n + 3)) = 3 := rfl
@[simp] theorem succ_three_eq_four : Fin.succ (3 : Fin (n + 4)) = 4 := rfl
@[simp] theorem succ_four_eq_five : Fin.succ (4 : Fin (n + 5)) = 5 := rfl
@[simp] theorem succ_five_eq_six : Fin.succ (5 : Fin (n + 6)) = 6 := rfl
@[simp] theorem succ_six_eq_seven : Fin.succ (6 : Fin (n + 7)) = 7 := rfl
@[simp] theorem succ_seven_eq_eight : Fin.succ (7 : Fin (n + 8)) = 8 := rfl
@[simp] theorem succ_eight_eq_nine : Fin.succ (8 : Fin (n + 9)) = 9 := rfl
@[simp] theorem succ_nine_eq_ten : Fin.succ (9 : Fin (n + 10)) = 10 := rfl
@[simp] theorem succ_ten_eq_eleven : Fin.succ (10 : Fin (n + 11)) = 11 := rfl
@[simp] theorem succ_eleven_eq_twelve : Fin.succ (11 : Fin (n + 12)) = 12 := rfl

@[elab_as_elim] def cases1 {motive : Fin 1 → Sort _}
  (zero : motive 0) (i : Fin 1) : motive i := i.cases zero (·.elim0)
@[elab_as_elim] def cases2 {motive : Fin 2 → Sort _}
  (zero : motive 0) (one : motive 1) (i : Fin 2) : motive i :=
  i.cases zero λ i => i.cases one (·.elim0)
@[elab_as_elim] def cases3 {motive : Fin 3 → Sort _}
  (zero : motive 0) (one : motive 1) (two : motive 2)
  (i : Fin 3) : motive i :=
  i.cases zero λ i => i.cases one λ j => j.cases two (·.elim0)
@[elab_as_elim] def cases4 {motive : Fin 4 → Sort _}
  (zero : motive 0) (one : motive 1) (two : motive 2) (three : motive 3)
  (i : Fin 4) : motive i :=
  i.cases zero λ i => i.cases one λ j => j.cases two λ k => k.cases three (·.elim0)

attribute [simp] forall_fin_one forall_fin_two exists_fin_one exists_fin_two
@[simp] theorem forall_fin_three {p : Fin 3 → Prop} : (∀ (i : Fin 3), p i) ↔ p 0 ∧ p 1 ∧ p 2 := by simp [forall_fin_succ]
@[simp] theorem forall_fin_four {p : Fin 4 → Prop} : (∀ (i : Fin 4), p i) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 := by simp [forall_fin_succ]
@[simp] theorem exists_fin_three {p : Fin 3 → Prop} : (∃ (i : Fin 3), p i) ↔ p 0 ∨ p 1 ∨ p 2 := by simp [exists_fin_succ]
@[simp] theorem exists_fin_four {p : Fin 4 → Prop} : (∃ (i : Fin 4), p i) ↔ p 0 ∨ p 1 ∨ p 2 ∨ p 3 := by simp [exists_fin_succ]

/--
  `castAdd' x m` embeds `x : Fin n` in `Fin (m + n)`. This is contrary to `castAdd m i` which embeds
  into `Fin (n + m)`.
  -/
def castAdd' (x : Fin n) (m : ℕ) : Fin (m + n) := (x.castAdd m).cast (Nat.add_comm _ _)
@[simp] theorem castAdd'_zero : castAdd' (0 : Fin (n + 1)) m = (0 : Fin (m + n + 1)) := rfl
@[simp] theorem castAdd'_succ : castAdd' (succ x) m = succ (castAdd' x m) := rfl

@[simp] theorem addNat_succ : addNat x (m + 1) = succ (addNat x m) := rfl

theorem castAdd'_or_addNat (x : Fin (n + m)) : (∃ y, x = castAdd' y n) ∨ ∃ y, x = addNat y m := by
  by_cases h : x < m
  · left; exists ⟨x, h⟩
  · right; simp at h
    exists ⟨x - m, by simp [Nat.sub_lt_iff_lt_add h, Nat.add_comm m n]⟩
    simp [←val_inj, Nat.sub_add_cancel h]

end Fin

/-- `Vec α n` is an abbreviation of `Fin n → α` -- a vector of length `n`. -/
@[reducible] def Vec (α : Type u) (n : ℕ) := Fin n → α

namespace Vec

variable {α : Type u}

def nil : Vec α 0 := Fin.elim0
def cons (a : α) (v : Vec α n) : Vec α (n + 1) := Fin.cons a v
infixr:67 " ∷ᵥ " => cons
syntax (name := vec) "[" term,* "]ᵥ" : term
macro_rules
| `([$t:term, $ts:term,*]ᵥ) => `(cons $t [$ts,*]ᵥ)
| `([$t:term]ᵥ) => `(cons $t []ᵥ)
| `([]ᵥ) => `(nil)

@[simp] theorem cons_succ : (a ∷ᵥ v) i.succ = v i := rfl
@[simp] theorem cons_zero : (a ∷ᵥ v) 0 = a := rfl
@[simp] theorem cons_one {v : Vec α (n + 1)} : (a ∷ᵥ v) 1 = v 0 := rfl
@[simp] theorem cons_two {v : Vec α (n + 2)} : (a ∷ᵥ v) 2 = v 1 := rfl
@[simp] theorem cons_three {v : Vec α (n + 3)} : (a ∷ᵥ v) 3 = v 2 := rfl
@[simp] theorem cons_four {v : Vec α (n + 4)} : (a ∷ᵥ v) 4 = v 3 := rfl
@[simp] theorem cons_five {v : Vec α (n + 5)} : (a ∷ᵥ v) 5 = v 4 := rfl
@[simp] theorem cons_six {v : Vec α (n + 6)} : (a ∷ᵥ v) 6 = v 5 := rfl
@[simp] theorem cons_seven {v : Vec α (n + 7)} : (a ∷ᵥ v) 7 = v 6 := rfl
@[simp] theorem cons_eight {v : Vec α (n + 8)} : (a ∷ᵥ v) 8 = v 7 := rfl
@[simp] theorem cons_nine {v : Vec α (n + 9)} : (a ∷ᵥ v) 9 = v 8 := rfl
@[simp] theorem cons_ten {v : Vec α (n + 10)} : (a ∷ᵥ v) 10 = v 9 := rfl
@[simp] theorem cons_eleven {v : Vec α (n + 11)} : (a ∷ᵥ v) 11 = v 10 := rfl
@[simp] theorem cons_twelve {v : Vec α (n + 12)} : (a ∷ᵥ v) 12 = v 11 := rfl

@[app_unexpander nil] def unexpandNil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `([]ᵥ)

@[app_unexpander cons] def unexpandCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $tail) =>
    match tail with
    | `([]ᵥ)      => `([$x]ᵥ)
    | `([$xs,*]ᵥ) => `([$x, $xs,*]ᵥ)
    | `(⋯)       => `($x ∷ᵥ $tail)
    | _          => throw ()
  | _ => throw ()

@[ext] theorem ext {v₁ v₂ : Vec α n} :
  (∀ i, v₁ i = v₂ i) → v₁ = v₂ := funext

def head (v : Vec α (n + 1)) := v 0
@[simp] theorem head_cons : (a ∷ᵥ v).head = a := rfl
def tail (v : Vec α (n + 1)) : Vec α n := v ∘ Fin.succ
@[simp] theorem tail_app {v : Vec α (n + 1)} : v.tail x = v x.succ := rfl
@[simp] theorem tail_cons : (a ∷ᵥ v).tail = v := rfl

@[simp] theorem cons_eq_iff : a₁ ∷ᵥ v₁ = a₂ ∷ᵥ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ := by
  constructor
  · intro h
    rw [←head_cons (a := a₁), ←tail_cons (v := v₁), h]; simp
  · intro ⟨h₁, h₂⟩
    simp [h₁, h₂]

theorem eq_nil (v : Vec α 0) : v = []ᵥ := by
  ext x; exact x.elim0
theorem eq_cons (v : Vec α (n + 1)) : v = v.head ∷ᵥ v.tail := by
  ext x; cases x using Fin.cases <;> simp [cons, head, tail]
theorem eq_one (v : Vec α 1) : v = [v 0]ᵥ := by
  rw [eq_cons v, eq_nil v.tail]; rfl
theorem eq_two (v : Vec α 2) : v = [v 0, v 1]ᵥ := by
  rw [eq_cons v, eq_one v.tail]; rfl
theorem eq_three (v : Vec α 3) : v = [v 0, v 1, v 2]ᵥ := by
  rw [eq_cons v, eq_two v.tail]; rfl
theorem eq_four (v : Vec α 4) : v = [v 0, v 1, v 2, v 3]ᵥ := by
  rw [eq_cons v, eq_three v.tail]; rfl

open Lean Parser Tactic in
macro "simp_vec" g:(location)? : tactic =>
  `(tactic| repeat rw [Vec.eq_cons λ _ => _] $(g)?; simp [Vec.head, Vec.tail, Function.comp_def, Vec.eq_nil] $(g)?)

theorem exists_vec_succ {p : Vec α (n + 1) → Prop} : (∃ v, p v) ↔ ∃ a v, p (a ∷ᵥ v) := Fin.exists_fin_succ_pi (P := p)
@[simp high] theorem exists_vec0 {p : Vec α 0 → Prop} : (∃ v, p v) ↔ p []ᵥ := by simp [Vec.eq_nil]
@[simp] theorem exists_vec1 {p : Vec α 1 → Prop} : (∃ v, p v) ↔ ∃ x, p [x]ᵥ := by simp [exists_vec_succ]
@[simp] theorem exists_vec2 {p : Vec α 2 → Prop} : (∃ v, p v) ↔ ∃ x y, p [x, y]ᵥ := by simp [exists_vec_succ]
@[simp] theorem exists_vec3 {p : Vec α 3 → Prop} : (∃ v, p v) ↔ ∃ x y z, p [x, y, z]ᵥ := by simp [exists_vec_succ]

section

variable {motive : {n : ℕ} → Vec α n → Sort v}
  (nil : motive []ᵥ)
  (cons : {n : ℕ} → (a : α) → (v : Vec α n) → motive v → motive (a ∷ᵥ v))

@[elab_as_elim, induction_eliminator] def rec : {n : ℕ} → (v : Vec α n) → motive v
| 0, v => eq_nil v ▸ nil
| (_ + 1), v => eq_cons v ▸ cons v.head v.tail (rec v.tail)
@[simp] theorem rec_nil : rec nil cons []ᵥ = nil := rfl
@[simp] theorem rec_cons : rec nil cons (a ∷ᵥ v) = cons a v (rec nil cons v) := rfl

end

theorem comp_cons : f ∘ (a ∷ᵥ v) = f a ∷ᵥ f ∘ v := by
  ext x; cases x using Fin.cases <;> rfl

def rcons (v : Vec α n) (x : α) : Vec α (n + 1) := Fin.snoc v x
@[simp] theorem rcons_nil : rcons []ᵥ x = [x]ᵥ := by
  simp [rcons, Fin.snoc_zero]
  ext i; cases i using Fin.cases1; simp
@[simp] theorem rcons_cons : rcons (x ∷ᵥ v) y = x ∷ᵥ rcons v y := by
  simp [rcons, Vec.cons, Fin.cons_snoc_eq_snoc_cons]
@[simp] theorem rcons_last : rcons v a (Fin.last _) = a := Fin.snoc_last _ _
@[simp] theorem rcons_castSucc : rcons v a (Fin.castSucc x) = v x := Fin.snoc_castSucc _ _ _

/--
  `append v₁ v₂` adds elements in `v₁ : Vec α n` before elements in `v₂ : Vec α m`, but gets a vector
  of length `m + n`. This is contrary to `Fin.append` which returns vector of `n + m`.
  -/
def append (v₁ : Vec α n) (v₂ : Vec α m) : Vec α (m + n) :=
  match n with
  | 0 => v₂
  | _ + 1 => v₁.head ∷ᵥ v₁.tail.append v₂
infixl:65 " ++ᵥ " => append
@[simp] theorem nil_append : []ᵥ ++ᵥ v = v := rfl
@[simp] theorem cons_append : a ∷ᵥ v₁ ++ᵥ v₂ = a ∷ᵥ (v₁ ++ᵥ v₂) := rfl
@[simp] theorem append_left {v₂ : Vec α m} : (v₁ ++ᵥ v₂) (Fin.castAdd' x m) = v₁ x := by
  induction v₁ with
  | nil => exact x.elim0
  | cons a v₁ ih => cases x using Fin.cases <;> simp [ih]
@[simp] theorem append_right {v₁ : Vec α n} : (v₁ ++ᵥ v₂) (Fin.addNat x n) = v₂ x := by
  induction v₁ with
  | nil => simp
  | cons a v₁ ih => simp [ih]
theorem eq_append (v : Vec α (m + n)) : v = (λ i => v (i.castAdd' m)) ++ᵥ λ i => v (i.addNat n) := by
  ext x; rcases x.castAdd'_or_addNat with (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> simp

instance decEq [DecidableEq α] : DecidableEq (Vec α n) := by
  intro v₁ v₂
  induction n with
  | zero => rw [eq_nil v₁, eq_nil v₂]; exact isTrue rfl
  | succ n ih =>
    rw [eq_cons v₁, eq_cons v₂, cons_eq_iff]
    have := ih v₁.tail v₂.tail
    infer_instance

def max : {n : ℕ} → Vec ℕ n → ℕ
| 0, _ => 0
| _ + 1, v => Nat.max v.head v.tail.max

theorem le_max {v : Vec ℕ n} (i) : v i ≤ v.max := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => apply Nat.le_max_left
    | succ => rw [←tail_app (v := v)]; apply Nat.le_trans (ih _); apply Nat.le_max_right

theorem max_le {v : Vec ℕ n} : (∀ i, v i ≤ m) → v.max ≤ m := by
  intro h
  induction n with simp [max]
  | succ n ih =>
    constructor
    · apply h
    · apply ih; intro; apply h

theorem max_le_iff {v : Vec ℕ n} : v.max ≤ m ↔ ∀ i, v i ≤ m := by
  constructor
  · intro h i; exact le_trans (le_max i) h
  · exact max_le

@[simp] theorem max_zero : max (n := n) (λ _ => 0) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply max_le
  simp

theorem max_eq_nth (v : Vec ℕ (n + 1)) : ∃ i, v.max = v i := by
  induction n with
  | zero => simp [max, Vec.head]
  | succ n ih =>
    rw [max]
    by_cases h : v.head ≤ v.tail.max
    · simp [Nat.max_eq_right h]
      rcases ih v.tail with ⟨i, h'⟩
      exists i.succ
    · simp [Nat.max_eq_left (Nat.le_of_not_ge h)]; exists 0

theorem le_max_iff {v : Vec ℕ (n + 1)} : m ≤ v.max ↔ ∃ i, m ≤ v i := by
  constructor
  · intro h; rcases v.max_eq_nth with ⟨i, h'⟩; exists i; rw [←h']; exact h
  · intro ⟨i, h⟩; apply le_trans h; exact le_max i

theorem max_pos_iff {v : Vec ℕ n} : v.max > 0 ↔ ∃ i, v i > 0 := by
  induction n with simp [max]
  | succ n ih => simp [ih, head, Fin.exists_fin_succ]

theorem max_zero_iff {v : Vec ℕ n} : v.max = 0 ↔ ∀ i, v i = 0 := by
  induction n with simp [max]
  | succ n ih => simp [ih, head, Fin.forall_fin_succ]

/-- `paired [a₁, ⋯, aₙ]ᵥ` is `⟪a₁, ⟪a₂, ⟪⋯, ⟪aₙ, 0⟫⟫⟫` where `⟪x, y⟫` is `Nat.pair`. -/
def paired : {n : ℕ} → Vec ℕ n → ℕ
| 0, _ => 0
| _ + 1, v => v.head.pair v.tail.paired

theorem le_paired {v : Vec ℕ n} : v i ≤ v.paired := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp [paired]
    cases i using Fin.cases with
    | zero => apply Nat.left_le_pair
    | succ i => exact le_trans (ih (v := v.tail)) (Nat.right_le_pair _ _)

theorem paired_le_paired {v₁ v₂ : Vec ℕ n} : (∀ i, v₁ i ≤ v₂ i) → v₁.paired ≤ v₂.paired := by
  intro h
  induction n with simp [paired]
  | succ n ih =>
    apply Nat.pair_le_pair
    · apply h
    · apply ih; intro; apply h

@[simp] theorem paired_nil {v : Vec ℕ 0} : v.paired = 0 := rfl
@[simp] theorem unpair_paired {v : Vec ℕ (n + 1)} : v.paired.unpair = (v.head, v.tail.paired) := by simp [paired]

section

variable [Encodable α]

def encode (v : Vec α n) := paired λ i => Encodable.encode (v i)

def decode : (n k : ℕ) → Option (Vec α n)
| 0, k => if k = 0 then some []ᵥ else none
| n + 1, k => do
  let a ← Encodable.decode k.unpair.1
  let v ← decode n k.unpair.2
  some (a ∷ᵥ v)

theorem encode_decode {v : Vec α n} : decode n v.encode = some v := by
  induction n with simp [encode, decode, paired]
  | zero => simp [eq_nil]
  | succ n ih =>
    simp [head, tail, Function.comp_def]
    rw [←encode, ih, eq_cons v]; rfl

instance encodable : Encodable (Vec α n) where
  encode v := v.encode
  decode k := decode n k
  encodek _ := encode_decode

@[simp] theorem encode_nil {v : Vec α 0} : Encodable.encode v = 0 := rfl
@[simp] theorem encode_cons {v : Vec α n} : Encodable.encode (a ∷ᵥ v) = (Encodable.encode a).pair (Encodable.encode v) := rfl
theorem encode_eq {v : Vec α n} : Encodable.encode v = Vec.paired λ i => Encodable.encode (v i) := rfl

end

instance [Countable α] : Countable (Vec α n) :=
  have := Encodable.ofCountable
  inferInstance

def toList (v : Vec α n) : List α :=
  match n, v with
  | 0, _ => []
  | _ + 1, v => v.head :: v.tail.toList

open Std in
instance [Repr α] : Repr (Vec α n) where
  reprPrec v _ := Format.bracketFill "[" (Format.joinSep (Vec.toList (repr ∘ v)) ", ") "]ᵥ"

end Vec

