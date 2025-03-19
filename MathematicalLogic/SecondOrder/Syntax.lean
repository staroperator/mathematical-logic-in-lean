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
| var : Γ.Fin Ty.var → L.Term Γ
| fconst : L.Func n → (Fin n → L.Term Γ) → L.Term Γ
| fvar : Γ.Fin (Ty.func n) → (Fin n → L.Term Γ) → L.Term Γ
prefix:max "#" => Term.var
infix:70 " ⬝ᶠ " => Term.fconst
infix:70 " ⬝ᶠᵛ " => Term.fvar

inductive Formula (L : Language) : List Ty → Type where
| rconst {Γ n} : L.Rel n → (Fin n → L.Term Γ) → L.Formula Γ
| rvar {Γ n} : Γ.Fin (Ty.rel n) → (Fin n → L.Term Γ) → L.Formula Γ
| eq : L.Term Γ → L.Term Γ → L.Formula Γ
| false : L.Formula Γ
| imp : L.Formula Γ → L.Formula Γ → L.Formula Γ
| all : L.Formula (Ty.var :: Γ) → L.Formula Γ
| allf {Γ} (n) : L.Formula (Ty.func n :: Γ) → L.Formula Γ
| allr {Γ} (n) : L.Formula (Ty.rel n :: Γ) → L.Formula Γ

namespace Formula

infix:70 " ⬝ʳ " => rconst
infix:70 " ⬝ʳᵛ " => rvar
infix:60 (priority := high) " ≐ " => eq
instance : ClassicalPropNotation (L.Formula Γ) := ⟨false, imp⟩

notation "∀' " => all
notation "∀ᶠ " => allf
notation "∀ʳ " => allr
def ex (p : L.Formula (_ :: Γ)) := ~ ∀' (~ p)
def exf (n) (p : L.Formula (_ :: Γ)) := ~ ∀ᶠ n (~ p)
def exr (n) (p : L.Formula (_ :: Γ)) := ~ ∀ʳ n (~ p)
notation "∃' " => ex
notation "∃ᶠ " => exf
notation "∃ʳ " => exr

@[simp] theorem false_eq : false = (⊥ : L.Formula n) := rfl
@[simp] theorem imp_eq : imp p q = p ⇒ q := rfl

end Formula

abbrev Sentence (L : Language) := L.Formula []
abbrev Theory (L : Language) := Set L.Sentence

end SecondOrder.Language
