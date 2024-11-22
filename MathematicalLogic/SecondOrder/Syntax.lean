import MathematicalLogic.Vec
import MathematicalLogic.Notation

namespace SecondOrder

structure Language where
  Func : ℕ → Type
  Rel : ℕ → Type

inductive Ty where
| var : Ty
| func : ℕ → Ty
| rel : ℕ → Ty

def Context := List Ty
inductive Context.Mem : Ty → Context → Type where
| fz : Mem T (T :: Γ)
| fs : Mem T Γ → Mem T (T' :: Γ)
infix:55 " ∈ᶜ " => Context.Mem
instance : OfNat (x ∈ᶜ x :: l) 0 := ⟨.fz⟩
instance : OfNat (y ∈ᶜ x :: y :: l) 1 := ⟨.fs .fz⟩
instance : OfNat (z ∈ᶜ x :: y :: z :: l) 2 := ⟨.fs (.fs .fz)⟩
instance : OfNat (a ∈ᶜ x :: y :: z :: a :: l) 3 := ⟨.fs (.fs (.fs .fz))⟩
instance : OfNat (b ∈ᶜ x :: y :: z :: a :: b :: l) 4 := ⟨.fs (.fs (.fs (.fs .fz)))⟩

namespace Language

inductive Term (𝓛 : Language) : Context → Type where
| var {Γ} : Ty.var ∈ᶜ Γ → 𝓛.Term Γ
| fconst {Γ n} : 𝓛.Func n → (Fin n → 𝓛.Term Γ) → 𝓛.Term Γ
| fvar {Γ n} : Ty.func n ∈ᶜ Γ → (Fin n → 𝓛.Term Γ) → 𝓛.Term Γ
prefix:max "#" => Term.var
infix:70 " ⬝ᶠ " => Term.fconst
infix:70 " ⬝ᶠᵛ " => Term.fvar

inductive Formula (𝓛 : Language) : Context → Type where
| rconst {Γ n} : 𝓛.Rel n → (Fin n → 𝓛.Term Γ) → 𝓛.Formula Γ
| rvar {Γ n} : Ty.rel n ∈ᶜ Γ → (Fin n → 𝓛.Term Γ) → 𝓛.Formula Γ
| eq : 𝓛.Term Γ → 𝓛.Term Γ → 𝓛.Formula Γ
| false : 𝓛.Formula Γ
| imp : 𝓛.Formula Γ → 𝓛.Formula Γ → 𝓛.Formula Γ
| all : 𝓛.Formula (Ty.var :: Γ) → 𝓛.Formula Γ
| allf {Γ} (n) : 𝓛.Formula (Ty.func n :: Γ) → 𝓛.Formula Γ
| allr {Γ} (n) : 𝓛.Formula (Ty.rel n :: Γ) → 𝓛.Formula Γ
infix:70 " ⬝ʳ " => Formula.rconst
infix:70 " ⬝ʳᵛ " => Formula.rvar
infix:60 (priority := high) " ≐ " => Formula.eq
variable {𝓛 : Language}
instance : PropNotation (𝓛.Formula Γ) where
  false := Formula.false
  imp := Formula.imp
notation "∀' " => Formula.all
notation "∀ᶠ " => Formula.allf
notation "∀ʳ " => Formula.allr
abbrev Formula.exist (p : 𝓛.Formula (_ :: Γ)) := ~ ∀' (~ p)
abbrev Formula.existr (n) (p : 𝓛.Formula (_ :: Γ)) := ~ ∀ʳ n (~ p)
abbrev Formula.existf (n) (p : 𝓛.Formula (_ :: Γ)) := ~ ∀ᶠ n (~ p)
notation "∃' " => Formula.exist
notation "∃ᶠ " => Formula.existf
notation "∃ʳ " => Formula.existr

abbrev Sentence (𝓛 : Language) := 𝓛.Formula []
abbrev Theory (𝓛 : Language) := Set 𝓛.Sentence

end SecondOrder.Language
