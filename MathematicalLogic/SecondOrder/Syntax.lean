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

variable {𝓛 : Language}

inductive Term (𝓛 : Language) : List Ty → Type where
| var : Γ.Fin Ty.var → 𝓛.Term Γ
| fconst : 𝓛.Func n → (Fin n → 𝓛.Term Γ) → 𝓛.Term Γ
| fvar : Γ.Fin (Ty.func n) → (Fin n → 𝓛.Term Γ) → 𝓛.Term Γ
prefix:max "#" => Term.var
infix:70 " ⬝ᶠ " => Term.fconst
infix:70 " ⬝ᶠᵛ " => Term.fvar

inductive Formula (𝓛 : Language) : List Ty → Type where
| rconst {Γ n} : 𝓛.Rel n → (Fin n → 𝓛.Term Γ) → 𝓛.Formula Γ
| rvar {Γ n} : Γ.Fin (Ty.rel n) → (Fin n → 𝓛.Term Γ) → 𝓛.Formula Γ
| eq : 𝓛.Term Γ → 𝓛.Term Γ → 𝓛.Formula Γ
| false : 𝓛.Formula Γ
| imp : 𝓛.Formula Γ → 𝓛.Formula Γ → 𝓛.Formula Γ
| all : 𝓛.Formula (Ty.var :: Γ) → 𝓛.Formula Γ
| allf {Γ} (n) : 𝓛.Formula (Ty.func n :: Γ) → 𝓛.Formula Γ
| allr {Γ} (n) : 𝓛.Formula (Ty.rel n :: Γ) → 𝓛.Formula Γ

namespace Formula

infix:70 " ⬝ʳ " => rconst
infix:70 " ⬝ʳᵛ " => rvar
infix:60 (priority := high) " ≐ " => eq
instance : PropNotation (𝓛.Formula Γ) where
  false := false
  imp := imp

notation "∀' " => all
notation "∀ᶠ " => allf
notation "∀ʳ " => allr
def ex (p : 𝓛.Formula (_ :: Γ)) := ~ ∀' (~ p)
def exf (n) (p : 𝓛.Formula (_ :: Γ)) := ~ ∀ᶠ n (~ p)
def exr (n) (p : 𝓛.Formula (_ :: Γ)) := ~ ∀ʳ n (~ p)
notation "∃' " => ex
notation "∃ᶠ " => exf
notation "∃ʳ " => exr

@[simp] theorem false_eq : false = (⊥ : 𝓛.Formula n) := rfl
@[simp] theorem imp_eq : imp p q = p ⇒ q := rfl

end Formula

abbrev Sentence (𝓛 : Language) := 𝓛.Formula []
abbrev Theory (𝓛 : Language) := Set 𝓛.Sentence

end SecondOrder.Language
