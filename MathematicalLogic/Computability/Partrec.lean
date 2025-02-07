import Mathlib.Data.PFun
import MathematicalLogic.Computability.Primrec

namespace Mu

variable (f : Vec ℕ (k + 1) → Part ℕ) (v : Vec ℕ k)

def find
  (h : ∃ n, (∃ x, x + 1 ∈ f (n ∷ᵥ v)) ∧ ∀ k < n, (f (k ∷ᵥ v)).Dom)
  (n : ℕ) (ih : ∀ k < n, 0 ∈ f (k ∷ᵥ v)) :
  {n : ℕ // (∃ x, x + 1 ∈ f (n ∷ᵥ v)) ∧ ∀ k < n, 0 ∈ f (k ∷ᵥ v)} :=
  have h₁ : n ≤ Classical.choose h := by
    rcases (Classical.choose_spec h).left with ⟨x, h₁⟩
    by_contra h₂
    simp at h₂
    apply ih at h₂
    have := Part.mem_unique h₁ h₂
    contradiction
  have h₂ : (f (n ∷ᵥ v)).Dom := by
    apply Nat.eq_or_lt_of_le at h₁
    rcases h₁ with h₁ | h₁
    · rw [Part.dom_iff_mem, h₁]
      rcases (Classical.choose_spec h).left with ⟨x, h₂⟩
      exists x + 1
    · apply (Classical.choose_spec h).right
      exact h₁
  match h₃ : (f (n ∷ᵥ v)).get h₂ with
  | 0 =>
    have h₄ : n < Classical.choose h := by
      by_contra h₄
      apply eq_of_ge_of_not_gt h₁ at h₄
      rcases (Classical.choose_spec h).left with ⟨y, h₅⟩
      rw [h₄] at h₅
      apply Part.mem_unique (Part.get_mem h₂) at h₅
      simp [h₅] at h₃
    find h (n + 1) (by
      intros k h₅
      rw [Nat.add_one, Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at h₅
      rcases h₅ with h₅ | h₅
      · apply ih; exact h₅
      · rw [h₅, ←h₃]
        apply Part.get_mem)
  | x + 1 => ⟨n, ⟨x, by rw [Nat.add_one, ←h₃]; apply Part.get_mem⟩, ih⟩
termination_by Classical.choose h - n

def mu : Part ℕ := ⟨_, λ h => find f v h 0 (by simp)⟩

theorem mem_mu_iff : n ∈ mu f v ↔ (∃ x, x + 1 ∈ f (n ∷ᵥ v)) ∧ ∀ k < n, 0 ∈ f (k ∷ᵥ v) := by
  constructor
  · intro ⟨h₁, h₂⟩
    simp_rw [←h₂]
    exact (find f v _ 0 _).property
  · intro ⟨⟨x, h₁⟩, h₂⟩
    have h₃ : (mu f v).Dom := by
      simp [mu]
      exists n
      constructor
      · exists x
      · intro k h₃
        rcases h₂ k h₃ with ⟨h₄, _⟩
        exact h₄
    let m := (mu f v).get h₃
    rcases lt_trichotomy m n with h₄ | h₄ | h₄
    · apply h₂ at h₄
      rcases (find f v _ 0 _).property.left with ⟨x, h₅⟩
      apply Part.mem_unique h₅ at h₄
      contradiction
    · simp_rw [←h₄]; apply Part.get_mem
    · apply (find f v _ 0 _).property.right at h₄
      apply Part.mem_unique h₁ at h₄
      contradiction

theorem mu_dom : (mu f v).Dom ↔ ∃ n, (∃ x, x + 1 ∈ f (n ∷ᵥ v)) ∧ ∀ k < n, (f (k ∷ᵥ v)).Dom := by
  simp [mu]

end Mu

namespace Vec

def bindPart (v : Vec (Part α) n) : Part (Vec α n) :=
  ⟨∀ i, (v i).Dom, λ h i => (v i).get (h i)⟩

theorem bindPart_dom : (bindPart v).Dom ↔ ∀ i, (v i).Dom := by rfl

theorem bindPart_some : bindPart (λ i => Part.some (v i)) = Part.some v := by
  simp [bindPart, Part.eq_some_iff]

theorem bindPart_mem_iff : v ∈ bindPart w ↔ ∀ i, v i ∈ w i := by
  simp [Vec.bindPart]
  constructor
  · intro ⟨h₁, h₂⟩ i; subst h₂; simp; apply Part.get_mem
  · intro h₁; exists λ i => (h₁ i).1
    funext i; apply Part.get_eq_of_mem; apply h₁

theorem bindPart_get : (bindPart v).get h = λ i => (v i).get (h i) := rfl

end Vec

inductive Partrec : ℕ → Type where
| const : ℕ → Partrec n
| succ : Partrec 1
| proj : Fin n → Partrec n
| comp : Partrec n → (Fin n → Partrec m) → Partrec m
| prec : Partrec n → Partrec (n + 2) → Partrec (n + 1)
| mu : Partrec (n + 1) → Partrec n

namespace Partrec

abbrev comp₁ (f : Partrec 1) (g : Partrec n) := f.comp [g]ᵥ
abbrev comp₂ (f : Partrec 2) (g₁ g₂ : Partrec n) := f.comp [g₁, g₂]ᵥ
abbrev comp₃ (f : Partrec 3) (g₁ g₂ g₃ : Partrec n) := f.comp [g₁, g₂, g₃]ᵥ

def eval : Partrec n → Vec ℕ n →. ℕ
| const n, _ => Part.some n
| succ, v => Part.some v.head.succ
| proj i, v => Part.some (v i)
| comp f g, v => Vec.bindPart (λ i => (g i).eval v) >>= f.eval
| prec f g, v =>
  v.head.recOn (f.eval v.tail)
    (λ n ih => ih >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v.tail))
| mu f, v => Mu.mu f.eval v

instance : CoeFun (Partrec n) (λ _ => Vec ℕ n →. ℕ) := ⟨eval⟩
@[simp] theorem zero_eval : const n v = Part.some n := rfl
@[simp] theorem succ_eval : succ v = Part.some v.head.succ := rfl
@[simp] theorem proj_eval : (proj i) v = Part.some (v i) := rfl
@[simp] theorem comp_eval : (comp f g) v = Vec.bindPart (λ i => (g i).eval v) >>= f.eval := rfl
theorem prec_eval :
  (prec f g) v = v.head.recOn (f.eval v.tail)
    (λ n ih => ih >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v.tail)) := rfl
theorem prec_eval_zero : (prec f g) (0 ∷ᵥ v) = f.eval v := rfl
theorem prec_eval_succ : (prec f g) (n.succ ∷ᵥ v) = eval (prec f g) (n ∷ᵥ v) >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v) := rfl
@[simp] theorem mu_eval : eval (mu f) v = Mu.mu f.eval v := rfl

def Total (f : Partrec n) := ∀ v, (f v).Dom

def ofPrim : Primrec n → Partrec n
| .const n => const n
| .succ => succ
| .proj i => proj i
| .comp f g => comp (ofPrim f) (λ i => ofPrim (g i))
| .prec f g => prec (ofPrim f) (ofPrim g)
@[simp] theorem ofPrim_eval : (ofPrim f) v = Part.some (f v) := by
  induction f with simp [ofPrim]
  | comp f g ih₁ ih₂ =>
    rw [Part.eq_some_iff]
    simp [Vec.bindPart, ih₁, ih₂]
  | prec f g ih₁ ih₂ =>
    simp [Primrec.prec_eval, prec_eval, Vec.head]
    generalize v 0 = n, v.tail = v
    simp [ih₁, ih₂]
    induction n with simp
    | succ n ih => simp [ih]
theorem ofPrim_total : Total (ofPrim f) := by
  intro; simp

def loop : Partrec n := mu (ofPrim (.const 0))
@[simp] theorem loop_eval : loop v = Part.none := by
  simp [loop, Part.eq_none_iff]
  intro n h
  simp [Mu.mem_mu_iff] at h

open Lean.Parser Std in
def repr : Partrec n → ℕ → Format
| const n, _ => "const " ++ n.repr
| succ, _ => "succ"
| proj i, p => Repr.addAppParen ("proj " ++ reprPrec i maxPrec) p
| comp f v, p => Repr.addAppParen ("comp " ++ repr f maxPrec ++ " " ++ Format.bracketFill "[" (Format.joinSep (Vec.toList λ i => (v i).repr 0) (", ")) "]ᵥ") p
| prec f g, p => Repr.addAppParen ("prec " ++ repr f maxPrec ++ " " ++ repr g maxPrec) p
| mu f, p => Repr.addAppParen ("mu " ++ repr f maxPrec) p

instance : Repr (Partrec n) := ⟨repr⟩

end Partrec
