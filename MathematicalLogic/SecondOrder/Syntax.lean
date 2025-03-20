import MathematicalLogic.Vec
import MathematicalLogic.Notation

inductive List.Fin {α : Type u} : List α → α → Type u
| fz : Fin (a :: l) a
| fs : Fin l a → Fin (b :: l) a
instance : OfNat (List.Fin (a :: l) a) 0 := ⟨.fz⟩
instance : OfNat (List.Fin (a :: b :: l) b) 1 := ⟨.fs .fz⟩
instance : OfNat (List.Fin (a :: b :: c :: l) c) 2 := ⟨.fs (.fs .fz)⟩
instance : OfNat (List.Fin (a :: b :: c :: d :: l) d) 3 := ⟨.fs (.fs (.fs .fz))⟩
instance : OfNat (List.Fin (a :: b :: c :: d :: e :: l) e) 4 := ⟨.fs (.fs (.fs (.fs .fz)))⟩

namespace SecondOrder

structure Language where
  Func : ℕ → Type
  Rel : ℕ → Type

inductive Ty where
| var : Ty
| func : ℕ → Ty
| rel : ℕ → Ty

namespace Language

variable {L : Language}

inductive Term (L : Language) : List Ty → Type where
| var : l.Fin Ty.var → L.Term l
| fconst : L.Func n → (Fin n → L.Term l) → L.Term l
| fvar : l.Fin (Ty.func n) → (Fin n → L.Term l) → L.Term l
prefix:max "#" => Term.var
infix:70 " ⬝ᶠ " => Term.fconst
infix:70 " ⬝ᶠᵛ " => Term.fvar

inductive Formula (L : Language) : List Ty → Type where
| rconst : L.Rel n → (Fin n → L.Term l) → L.Formula l
| rvar : l.Fin (Ty.rel n) → (Fin n → L.Term l) → L.Formula l
| eq : L.Term l → L.Term l → L.Formula l
| false : L.Formula l
| imp : L.Formula l → L.Formula l → L.Formula l
| all : L.Formula (Ty.var :: l) → L.Formula l
| allf (n) : L.Formula (Ty.func n :: l) → L.Formula l
| allr (n) : L.Formula (Ty.rel n :: l) → L.Formula l

namespace Formula

infix:70 " ⬝ʳ " => rconst
infix:70 " ⬝ʳᵛ " => rvar
infix:60 " ≐ " => eq
instance : ClassicalPropNotation (L.Formula l) := ⟨false, imp⟩

prefix:100 "∀' " => all
notation:100 "∀ᶠ[" n "]" p:100 => allf n p
notation:100 "∀ʳ[" n "]" p:100 => allr n p
def ex (p : L.Formula (_ :: l)) := ~ ∀' (~ p)
def exf (n) (p : L.Formula (_ :: l)) := ~ ∀ᶠ[n] (~ p)
def exr (n) (p : L.Formula (_ :: l)) := ~ ∀ʳ[n] (~ p)
prefix:100 "∃' " => ex
notation:100 "∃ᶠ[" n "]" p:100 => exf n p
notation:100 "∃ʳ[" n "]" p:100 => exr n p

@[simp] theorem false_eq : false = (⊥ : L.Formula l) := rfl
@[simp] theorem imp_eq : imp p q = p ⇒ q := rfl

end Formula

abbrev Sentence (L : Language) := L.Formula []
abbrev Theory (L : Language) := Set L.Sentence

end SecondOrder.Language
