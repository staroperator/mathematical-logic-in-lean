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
| prec f g, v => Part.natrec (f.eval v.tail) (λ n ih => ih >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v.tail)) v.head
| mu f, v => Part.find λ n => f.eval (n ∷ᵥ v)

instance : CoeFun (Partrec n) (λ _ => Vec ℕ n →. ℕ) := ⟨eval⟩
@[simp] theorem zero_eval : const n v = Part.some n := rfl
@[simp] theorem succ_eval : succ v = Part.some v.head.succ := rfl
@[simp] theorem proj_eval : proj i v = Part.some (v i) := rfl
@[simp] theorem comp_eval : comp f g v = Part.bindVec (λ i => g i v) >>= f := rfl
theorem prec_eval : (prec f g) v = Part.natrec (f.eval v.tail) (λ n ih => ih >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v.tail)) v.head := rfl
theorem prec_eval_zero : (prec f g) (0 ∷ᵥ v) = f.eval v := Part.natrec_zero
theorem prec_eval_succ : (prec f g) (n.succ ∷ᵥ v) = eval (prec f g) (n ∷ᵥ v) >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v) := by
  simp [prec_eval, Part.natrec_succ]
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
    simp [Primrec.prec_eval, prec_eval, Vec.head, ih₁]
    generalize v 0 = n, v.tail = v
    induction n with simp [Part.natrec_zero, Part.natrec_succ]
    | succ n ih => simp [ih]; simp [ih₂]
theorem ofPrim_total : Total (ofPrim f) := by
  intro; simp

def loop : Partrec n := mu (ofPrim (.const 0))
@[simp] theorem loop_eval : loop v = Part.none := by
  simp [loop, Part.eq_none_iff]
  intro n h
  simp [Part.mem_find_iff, Part.zero_def] at h

def cov (f : Partrec (n + 2)) : Partrec (n + 1) :=
  (const 0).prec ((ofPrim .rcons).comp₃ (proj 0) (proj 1) f)
theorem cov_dom {f : Partrec (n + 2)} (hf : ∀ a b, (f (a ∷ᵥ b ∷ᵥ v)).Dom) :
  ∀ m, (f.cov (m ∷ᵥ v)).Dom := by
  intro m
  induction m with
  | zero => simp [cov, prec_eval_zero]
  | succ m ih =>
    rw [cov, prec_eval_succ, ←cov]
    simp; exists ih; apply hf
theorem cov_eval {f : Partrec (n + 2)} (hf : ∀ a b, (f (a ∷ᵥ b ∷ᵥ v)).Dom) :
  f.cov (m ∷ᵥ v) = Part.some (Vec.paired λ i : Fin m =>
    (f (i ∷ᵥ (f.cov (i ∷ᵥ v)).get (cov_dom hf _) ∷ᵥ v)).get (hf _ _)) := by
  induction m with
  | zero => simp [cov, prec_eval_zero, Vec.paired]
  | succ m ih =>
    nth_rw 1 [cov]; rw [prec_eval_succ, ←cov]
    simp [ih, Part.eq_some_iff]
    refine ⟨_, _, _, ⟨Part.get _ (hf _ _), Part.get_mem (hf _ _), rfl, rfl, rfl⟩, ?_⟩
    simp [Primrec.rcons_eval]
    congr! with i
    cases i using Fin.lastCases <;> simp [ih]

def covrec (f : Partrec (n + 2)) : Partrec (n + 1) :=
  (ofPrim .vget).comp₂ (f.cov.comp (succ.comp₁ (proj 0) ∷ᵥ (proj ·.succ))) (proj 0)
theorem covrec_dom {f : Partrec (n + 2)} (hf : ∀ a b, (f (a ∷ᵥ b ∷ᵥ v)).Dom) :
  ∀ m, (f.covrec (m ∷ᵥ v)).Dom := by
  intro m; simp [covrec, Fin.forall_fin_succ]; apply cov_dom hf
theorem covrec_eval {f : Partrec (n + 2)} (hf : ∀ a b, (f (a ∷ᵥ b ∷ᵥ v)).Dom) :
  f.covrec (m ∷ᵥ v) = f (m ∷ᵥ Vec.paired (λ i : Fin m => (f.covrec (i ∷ᵥ v)).get (covrec_dom hf _)) ∷ᵥ v) := by
  simp [covrec, Part.bindVec_some, Part.bindVec_cons, Vec.head, Vec.tail, Function.comp_def]
  rw [cov_eval hf]; simp [Primrec.vget_eval' (Nat.lt_succ_self m)]
  congr!; simp [Part.get_eq_iff_mem]; rw [cov_eval hf]; simp
  congr! with i; rw [cov_eval hf]; simp [Primrec.vget_eval']

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

abbrev Primrec.toPart : Primrec n → Partrec n := Partrec.ofPrim

variable {α : Type u} [Encodable α] {s : Set α}

class Recursive (s : Set α) where
  char : Partrec 1
  char_dom : ∀ (x : α), (char [Encodable.encode x]ᵥ).Dom
  mem_iff : ∀ x, x ∈ s ↔ 0 < char [Encodable.encode x]ᵥ

namespace Recursive

variable [Recursive s]

theorem not_mem_iff (x : α) :
  x ∉ s ↔ char s [Encodable.encode x]ᵥ = 0 := by
  rw [mem_iff x, ←Part.some_get (char_dom x)]
  simp [Part.zero_def, -Part.some_get]

def compl : Recursive sᶜ where
  char := (Primrec.nsign.toPart).comp₁ (char s)
  char_dom x := by simp; exact char_dom x
  mem_iff x := by simp; simp [not_mem_iff, Part.zero_def, Part.eq_some_iff]

def decidable : DecidablePred (· ∈ s) := by
  intro x
  simp [mem_iff x]
  rw [←Part.some_get (char_dom x)]
  simp [Part.zero_def, -Part.some_get]
  infer_instance

end Recursive

def IsRecursive (s : Set α) := Nonempty (Recursive s)

theorem IsRecursive.compl_iff : IsRecursive s ↔ IsRecursive sᶜ := by
  constructor
  · intro ⟨h⟩; exact ⟨Recursive.compl⟩
  · intro ⟨h⟩; rw [←compl_compl s]; exact ⟨Recursive.compl⟩

class Enumerable (s : Set α) where
  enum : Partrec 2
  enum_dom : ∀ n (x : α), (enum [n, Encodable.encode x]ᵥ).Dom
  mem_iff : ∀ x, x ∈ s ↔ ∃ n, 0 < enum [n, Encodable.encode x]ᵥ

theorem Enumerable.not_mem_iff [Enumerable s] (x : α) :
  x ∉ s ↔ ∀ n, enum s [n, Encodable.encode x]ᵥ = 0 := by
  rw [mem_iff x]; simp
  congr! with n
  rw [←Part.some_get (enum_dom n x)]
  simp [Part.zero_def, -Part.some_get]

instance Recursive.enumerable [Recursive s] : Enumerable s where
  enum := (char s).comp₁ (.proj 1)
  enum_dom n x := by simp [Vec.eq_one]; exact char_dom x
  mem_iff x := by simp [Vec.eq_one]; exact mem_iff x

def IsEnumerable (s : Set α) := Nonempty (Enumerable s)

theorem IsRecursive.enumerable : IsRecursive s → IsEnumerable s := by
  intro ⟨h⟩; exact ⟨h.enumerable⟩
