import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Pairing

@[elab_as_elim] def Fin.cases1 {motive : Fin 1 → Sort _}
  (zero : motive 0) (i : Fin 1) : motive i := i.cases zero (·.elim0)
@[elab_as_elim] def Fin.cases2 {motive : Fin 2 → Sort _}
  (zero : motive 0) (one : motive 1) (i : Fin 2) : motive i :=
  i.cases zero (λ i => i.cases one (·.elim0))
@[elab_as_elim] def Fin.cases3 {motive : Fin 3 → Sort _}
  (zero : motive 0) (one : motive 1) (two : motive 2)
  (i : Fin 3) : motive i :=
  i.cases zero (λ i => i.cases one (λ j => j.cases two (·.elim0)))

def Vec (α : Type u) (n : ℕ) := Fin n → α

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
@[simp] theorem cons_0 : (a ∷ᵥ v) 0 = a := rfl
@[simp] theorem cons_1 {v : Vec α (n + 1)} : (a ∷ᵥ v) 1 = v 0 := rfl
@[simp] theorem cons_2 {v : Vec α (n + 2)} : (a ∷ᵥ v) 2 = v 1 := rfl
@[simp] theorem cons_3 {v : Vec α (n + 3)} : (a ∷ᵥ v) 3 = v 2 := rfl

@[app_unexpander nil] def unexpandNil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `([]ᵥ)

@[app_unexpander cons] def unexpandCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $tail) =>
    match tail with
    | `([]ᵥ)      => `([$x]ᵥ)
    | `([$xs,*]ᵥ) => `([$x, $xs,*]ᵥ)
    | `(⋯)       => `([$x, $tail]ᵥ)
    | _          => throw ()
  | _ => throw ()

@[ext] theorem ext {v₁ v₂ : Vec α n} :
  (∀ i, v₁ i = v₂ i) → v₁ = v₂ := funext

theorem ext_iff {v₁ v₂ : Vec α n} :
  (∀ i, v₁ i = v₂ i) ↔ v₁ = v₂ := ⟨ext, congr_fun⟩

def head (v : Vec α (n + 1)) := v 0
@[simp] theorem head_cons : (a ∷ᵥ v).head = a := rfl
def tail (v : Vec α (n + 1)) : Vec α n := v ∘ Fin.succ
@[simp] theorem tail_app {v : Vec α (n + 1)} : v.tail x = v x.succ := rfl
@[simp] theorem tail_cons : (a ∷ᵥ v).tail = v := rfl

theorem cons_eq_iff : a₁ ∷ᵥ v₁ = a₂ ∷ᵥ v₂ ↔ a₁ = a₂ ∧ v₁ = v₂ := by
  constructor
  · intro h
    rw [←head_cons (a := a₁), ←tail_cons (v := v₁), h]; simp
  · intro ⟨h₁, h₂⟩
    simp [h₁, h₂]

theorem eq_nil (v : Vec α 0) : v = []ᵥ := by
  ext x; exact x.elim0
theorem eq_cons (v : Vec α (n + 1)) : v = v.head ∷ᵥ v.tail := by
  ext x; cases x using Fin.cases <;> simp [cons, head, tail]
theorem eq_1 (v : Vec α 1) : v = [v 0]ᵥ := by
  rw [eq_cons v, eq_nil v.tail]; rfl
theorem eq_2 (v : Vec α 2) : v = [v 0, v 1]ᵥ := by
  rw [eq_cons v, eq_1 v.tail]; rfl
theorem eq_3 (v : Vec α 3) : v = [v 0, v 1, v 2]ᵥ := by
  rw [eq_cons v, eq_2 v.tail]; rfl
theorem eq_4 (v : Vec α 4) : v = [v 0, v 1, v 2, v 3]ᵥ := by
  rw [eq_cons v, eq_3 v.tail]; rfl

section

variable {motive : {n : ℕ} → Vec α n → Sort v}
  (nil : motive []ᵥ)
  (cons : {n : ℕ} → (a : α) → (v : Vec α n) → motive v → motive (a ∷ᵥ v))

@[elab_as_elim] def rec : {n : ℕ} → (v : Vec α n) → motive v
| 0, v => eq_nil v ▸ nil
| (_ + 1), v => eq_cons v ▸ cons v.head v.tail (rec v.tail)
@[simp] theorem rec_nil : rec nil cons []ᵥ = nil := rfl
@[simp] theorem rec_cons : rec nil cons (a ∷ᵥ v) = cons a v (rec nil cons v) := rfl

end

@[simp] theorem comp_nil : f ∘ []ᵥ = []ᵥ := by ext x; exact x.elim0
@[simp] theorem comp_cons : f ∘ (a ∷ᵥ v) = f a ∷ᵥ f ∘ v := by
  ext x; cases x using Fin.cases <;> rfl
theorem comp_comp {v : Vec α n} : g ∘ (f ∘ v) = (g ∘ f) ∘ v := rfl

def rcons (v : Vec α n) (x : α) : Vec α (n + 1) := Fin.snoc v x
@[simp] theorem rcons_nil : rcons []ᵥ x = [x]ᵥ := by
  simp [rcons, Fin.snoc_zero]
  ext i; cases i using Fin.cases1; simp
@[simp] theorem rcons_cons : rcons (x ∷ᵥ v) y = x ∷ᵥ rcons v y := by
  simp [rcons, Vec.cons, Fin.cons_snoc_eq_snoc_cons]

def ofVector (v : Vector α n) : Vec α n := v.get
def toVector (v : Vec α n) : Vector α n := .ofFn v

instance decEq [DecidableEq α] : DecidableEq (Vec α n) := by
  intro v₁ v₂
  induction n with
  | zero => rw [eq_nil v₁, eq_nil v₂]; exact isTrue rfl
  | succ n ih =>
    rw [eq_cons v₁, eq_cons v₂, cons_eq_iff]
    have := ih v₁.tail v₂.tail
    exact And.decidable

def max : {n : ℕ} → Vec ℕ n → ℕ
| 0, _ => 0
| _ + 1, v => Nat.max v.head v.tail.max

theorem le_max {v : Vec ℕ n} : v i ≤ v.max := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => apply Nat.le_max_left
    | succ => rw [←tail_app (v := v)]; apply Nat.le_trans ih; apply Nat.le_max_right

theorem max_le {v : Vec ℕ n} : (∀ i, v i ≤ m) → v.max ≤ m := by
  intro h
  induction n with simp [max]
  | succ n ih =>
    constructor
    · apply h
    · apply ih; intro; apply h

theorem max_le_iff {v : Vec ℕ n} : v.max ≤ m ↔ ∀ i, v i ≤ m := by
  constructor
  · intro h i; exact le_trans le_max h
  · exact max_le

@[simp] theorem max_zero : max (n := n) (λ _ => 0) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply max_le
  simp

theorem max_eq_nth (v : Vec ℕ (n + 1)) : ∃ i, v.max = v i := by
  induction n with
  | zero => simp [max]; exists 0
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
  · intro ⟨i, h⟩; apply le_trans h; exact le_max

def paired : {n : ℕ} → Vec ℕ n → ℕ
| 0, _ => 0
| _ + 1, v => v.head.pair v.tail.paired

end Vec

