import MathematicalLogic.Part
import MathematicalLogic.Computability.Primrec

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
| comp f g, v => Part.bindVec (λ i => (g i).eval v) >>= f.eval
| prec f g, v =>
  v.head.recOn (f.eval v.tail)
    (λ n ih => ih >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v.tail))
| mu f, v => Part.find λ n => f.eval (n ∷ᵥ v)

instance : CoeFun (Partrec n) (λ _ => Vec ℕ n →. ℕ) := ⟨eval⟩
@[simp] theorem zero_eval : const n v = Part.some n := rfl
@[simp] theorem succ_eval : succ v = Part.some v.head.succ := rfl
@[simp] theorem proj_eval : proj i v = Part.some (v i) := rfl
@[simp] theorem comp_eval : comp f g v = Part.bindVec (λ i => g i v) >>= f := rfl
theorem prec_eval :
  (prec f g) v = v.head.recOn (f.eval v.tail)
    (λ n ih => ih >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v.tail)) := rfl
theorem prec_eval_zero : (prec f g) (0 ∷ᵥ v) = f.eval v := rfl
theorem prec_eval_succ : (prec f g) (n.succ ∷ᵥ v) = eval (prec f g) (n ∷ᵥ v) >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v) := rfl
@[simp] theorem mu_eval : mu f v = Part.find λ n => f.eval (n ∷ᵥ v) := rfl

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
    simp [Part.eq_some_iff]
    exists λ i => g i v
    simp [ih₁, ih₂]
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
  simp [Part.mem_find_iff, Part.zero_def] at h

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
