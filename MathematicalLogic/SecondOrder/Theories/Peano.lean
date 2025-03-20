import MathematicalLogic.SecondOrder.Semantics

namespace SecondOrder.Language

private inductive peano.Func : ℕ → Type where
| zero : Func 0
| succ : Func 1
| add : Func 2
| mul : Func 2

def peano : Language where
  Func := peano.Func
  Rel _ := Empty

namespace peano

instance : Zero (peano.Term l) := ⟨.zero ⬝ᶠ []ᵥ⟩
instance : Add (peano.Term l) := ⟨(.add ⬝ᶠ [·, ·]ᵥ)⟩
instance : Mul (peano.Term l) := ⟨(.mul ⬝ᶠ [·, ·]ᵥ)⟩

def succ (t : peano.Term l) : peano.Term l := .succ ⬝ᶠ [t]ᵥ
scoped prefix:max "S " => succ

instance Nat : peano.IsStructure ℕ where
  interpFunc
  | .zero, _ => 0
  | .succ, v => v 0 + 1
  | .add, v => v 0 + v 1
  | .mul, v => v 0 * v 1
  interpRel := nofun

namespace Nat

variable {t t₁ t₂ : peano.Term l}

@[simp] theorem interp_zero : ⟦ (0 : peano.Term l) ⟧ₜ ℕ, ρ = 0 := rfl
@[simp] theorem interp_succ : ⟦ S t ⟧ₜ ℕ, ρ = ⟦ t ⟧ₜ ℕ, ρ + 1 := rfl
@[simp] theorem interp_add : ⟦ t₁ + t₂ ⟧ₜ ℕ, ρ = ⟦ t₁ ⟧ₜ ℕ, ρ + ⟦ t₂ ⟧ₜ ℕ, ρ := rfl
@[simp] theorem interp_mul : ⟦ t₁ * t₂ ⟧ₜ ℕ, ρ = ⟦ t₁ ⟧ₜ ℕ, ρ * ⟦ t₂ ⟧ₜ ℕ, ρ := rfl

end peano.Nat

namespace Theory

open peano

inductive PA₂ : peano.Theory where
| ax_succ_ne_zero : PA₂ (∀' (~ S #0 ≐ 0))
| ax_succ_inj : PA₂ (∀' ∀' (S #1 ≐ S #0 ⇒ #1 ≐ #0))
| ax_add_zero : PA₂ (∀' (#0 + 0 ≐ #0))
| ax_add_succ : PA₂ (∀' ∀' (#1 + S #0 ≐ S (#1 + #0)))
| ax_mul_zero : PA₂ (∀' (#0 * 0 ≐ 0))
| ax_mul_succ : PA₂ (∀' ∀' (#1 * S #0 ≐ #1 * #0 + #1))
| ax_ind : PA₂ (∀ʳ[1] (0 ⬝ʳᵛ [0]ᵥ ⇒ (∀' (1 ⬝ʳᵛ [#0]ᵥ ⇒ 1 ⬝ʳᵛ [S #0]ᵥ)) ⇒ ∀' (1 ⬝ʳᵛ [#0]ᵥ)))

namespace PA₂

instance : PA₂.IsModel ℕ where
  satisfy_theory p h := by
    cases h with simp [Vec.eq_one]
    | ax_add_succ => intros; rfl
    | ax_mul_succ => intros; rfl
    | ax_ind =>
      intros r h₁ h₂ n
      induction n with
      | zero => exact h₁
      | succ n ih => exact h₂ _ ih

variable {M : PA₂.Model} {t t₁ t₂ : peano.Term l} {ρ : Assignment M l} {n m : ℕ}

instance : Zero M := ⟨M.interpFunc .zero []ᵥ⟩
instance : Add M := ⟨(M.interpFunc .add [·, ·]ᵥ)⟩
instance : Mul M := ⟨(M.interpFunc .mul [·, ·]ᵥ)⟩

def succ (u : M) := M.interpFunc .succ [u]ᵥ

@[simp] theorem interp_zero : ⟦ (0 : peano.Term l) ⟧ₜ M, ρ = 0 := by simp [OfNat.ofNat, Zero.zero, Vec.eq_nil]; rfl
@[simp] theorem interp_succ : ⟦ S t ⟧ₜ M, ρ = succ (⟦ t ⟧ₜ M, ρ) := by simp [peano.succ, succ, Vec.eq_one]; rfl
@[simp] theorem interp_add : ⟦ t₁ + t₂ ⟧ₜ M, ρ = ⟦ t₁ ⟧ₜ M, ρ + ⟦ t₂ ⟧ₜ M, ρ := by simp [HAdd.hAdd, Add.add, Vec.eq_two]; rfl
@[simp] theorem interp_mul : ⟦ t₁ * t₂ ⟧ₜ M, ρ = ⟦ t₁ ⟧ₜ M, ρ * ⟦ t₂ ⟧ₜ M, ρ := by simp [HMul.hMul, Mul.mul, Vec.eq_two]; rfl

def ofNat : ℕ → M
| 0 => 0
| n + 1 => succ (ofNat n)

theorem ofNat_injective : Function.Injective (@ofNat M) := by
  intro n m h₁
  by_contra h₂
  apply Nat.lt_or_gt_of_ne at h₂
  wlog h₃ : n < m
  · simp [h₃] at h₂
    apply this (M := M) _ _ h₂
    · rw [h₁]
    · simp [h₂]
  clear h₂
  cases' m with m <;> simp [Nat.lt_succ] at h₃
  induction n generalizing m with
  | zero =>
    have := M.satisfy_theory _ .ax_succ_ne_zero
    simp at this
    exact this _ h₁.symm
  | succ n ih =>
    have := M.satisfy_theory _ .ax_succ_inj
    simp at this; apply this at h₁
    cases' m with m <;> simp at h₃
    exact ih _ h₁ h₃

theorem ofNat_surjective : Function.Surjective (@ofNat M) := by
  intro u
  have := M.satisfy_theory _ .ax_ind
  simp [Vec.eq_one] at this
  apply this (r := λ v => ∃ n, ofNat n = v 0)
  · exists 0
  · intro u ⟨n, h₁⟩
    exists n.succ
    rw [ofNat, h₁]
    rfl

theorem ofNat_add : @ofNat M (n + m) = ofNat n + ofNat m := by
  symm
  induction m with
  | zero =>
    have := M.satisfy_theory _ .ax_add_zero
    simp at this; apply this
  | succ m ih =>
    have := M.satisfy_theory _ .ax_add_succ
    simp at this
    apply (this _ _).trans
    simp [ofNat, ←ih]

theorem ofNat_mul : @ofNat M (n * m) = ofNat n * ofNat m := by
  symm
  induction m with
  | zero =>
    have := M.satisfy_theory _ .ax_mul_zero
    simp at this; apply this
  | succ m ih =>
    have := M.satisfy_theory _ .ax_mul_succ
    simp at this
    apply (this _ _).trans
    simp [Nat.mul_succ, ofNat_add, ←ih]

theorem iso_Nat (M : PA₂.Model) : Nonempty (M.toStructure ≃ᴹ .of ℕ) := by
  refine ⟨.symm ⟨Equiv.ofBijective (@ofNat M) ⟨?_, ?_⟩, ?_, nofun⟩⟩
  · exact ofNat_injective
  · exact ofNat_surjective
  · intro _ f v
    cases f with
    | zero => simp [Vec.eq_nil]; rfl
    | succ => rw [Vec.eq_one (_ ∘ _)]; rfl
    | add => rw [Vec.eq_two (_ ∘ _)]; exact ofNat_add
    | mul => rw [Vec.eq_two (_ ∘ _)]; exact ofNat_mul

theorem categorical : PA₂.Categorical := by
  intro M₁ M₂
  rcases iso_Nat M₁ with ⟨i₁⟩
  rcases iso_Nat M₂ with ⟨i₂⟩
  exact ⟨i₁.trans i₂.symm⟩

end SecondOrder.Language.Theory.PA₂
