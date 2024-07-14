import MathematicalLogic.SecondOrder.Semantics

namespace SecondOrder.Language

inductive Peano.Func : ℕ → Type where
| zero : Func 0
| succ : Func 1
| add : Func 2
| mul : Func 2

def Peano : Language where
  Func := Peano.Func
  Rel _ := Empty

instance : Zero (Peano.Term Γ) := ⟨.zero ⬝ᶠ []ᵥ⟩
def Term.succ (t : Peano.Term Γ) : Peano.Term Γ := .succ ⬝ᶠ [t]ᵥ
instance : Add (Peano.Term Γ) := ⟨(.add ⬝ᶠ [·, ·]ᵥ)⟩
instance : Mul (Peano.Term Γ) := ⟨(.mul ⬝ᶠ [·, ·]ᵥ)⟩
local prefix:max "S " => Term.succ

namespace Theory

inductive PA : Peano.Theory where
| n1 : PA (∀' (~ S #0 ≐ 0))
| n2 : PA (∀' (∀' (S #1 ≐ S #0 ⇒ #1 ≐ #0)))
| n3 : PA (∀' (#0 + 0 ≐ #0))
| n4 : PA (∀' (∀' (#1 + S #0 ≐ S (#1 + #0))))
| n5 : PA (∀' (#0 * 0 ≐ 0))
| n6 : PA (∀' (∀' (#1 * S #0 ≐ #1 * #0 + #1)))
| n7 : PA (∀ʳ 1 (0 ⬝ʳᵛ [0]ᵥ ⇒ (∀' (1 ⬝ʳᵛ [#0]ᵥ ⇒ 1 ⬝ʳᵛ [S #0]ᵥ)) ⇒ ∀' (1 ⬝ʳᵛ [#0]ᵥ)))

attribute [local simp] Structure.satisfy Structure.interpFormula Structure.interpTerm Structure.Assignment.cons
  Vec.eq_two Vec.eq_one Vec.eq_nil

def PA.𝓝 : PA.Model where
  Dom := ℕ
  inhabited := inferInstance
  interpFunc
  | .zero, _ => 0
  | .succ, v => (v 0).succ
  | .add, v => v 0 + v 1
  | .mul, v => v 0 * v 1
  interpRel r := nomatch r
  satisfy_theory p h := by
    cases h with simp
    | n4 => intro n m; rfl
    | n6 => intro n m; rfl
    | n7 =>
      intros r h₁ h₂ n
      induction n with
      | zero => exact h₁
      | succ n ih => exact h₂ _ ih

namespace Model

variable {𝓜 : PA.Model}

instance : Zero 𝓜 := ⟨𝓜.interpFunc .zero []ᵥ⟩
def succ (u : 𝓜) := 𝓜.interpFunc .succ [u]ᵥ
def ofNat : ℕ → 𝓜
| 0 => 0
| n + 1 => 𝓜.succ (ofNat n)
instance : Add 𝓜 := ⟨(𝓜.interpFunc .add [·, ·]ᵥ)⟩
instance : Mul 𝓜 := ⟨(𝓜.interpFunc .mul [·, ·]ᵥ)⟩

theorem ofNat_injective : Function.Injective 𝓜.ofNat := by
  intro n m h₁
  by_contra h₂
  apply Nat.lt_or_gt_of_ne at h₂
  wlog h₃ : n < m
  · simp [h₃] at h₂
    apply this (𝓜 := 𝓜) _ _ h₂
    · rw [h₁]
    · simp [h₂]
  clear h₂
  cases' m with m <;> simp [Nat.lt_succ] at h₃
  induction n generalizing m with
  | zero =>
    have := 𝓜.satisfy_theory _ .n1
    simp at this; apply this; symm; exact h₁
  | succ n ih =>
    have := 𝓜.satisfy_theory _ .n2
    simp at this; apply this at h₁
    cases' m with m <;> simp at h₃
    exact ih _ h₁ h₃

theorem ofNat_surjective : Function.Surjective 𝓜.ofNat := by
  intro u
  have := 𝓜.satisfy_theory _ .n7
  simp at this
  apply this (r := λ v => ∃ n, 𝓜.ofNat n = v 0)
  · exists 0
  · intro u ⟨n, h₁⟩
    exists n.succ
    rw [ofNat, h₁]
    rfl

theorem ofNat_add : 𝓜.ofNat (n + m) = 𝓜.ofNat n + 𝓜.ofNat m := by
  symm
  induction m with
  | zero =>
    have := 𝓜.satisfy_theory _ .n3
    simp at this; apply this
  | succ m ih =>
    have := 𝓜.satisfy_theory _ .n4
    simp at this
    trans
    · apply this
    · simp_rw [Nat.add_succ, ofNat, ←ih]; rfl

theorem ofNat_mul : 𝓜.ofNat (n * m) = 𝓜.ofNat n * 𝓜.ofNat m := by
  symm
  induction m with
  | zero =>
    have := 𝓜.satisfy_theory _ .n5
    simp at this; apply this
  | succ m ih =>
    have := 𝓜.satisfy_theory _ .n6
    simp at this
    trans
    · apply this
    · simp [Nat.mul_succ, ofNat_add, ←ih]; rfl

end Model

namespace PA

noncomputable def model_iso_𝓝 (𝓜 : PA.Model) : 𝓝 ≃ᴹ 𝓜.toStructure where
  toEquiv := Equiv.ofBijective 𝓜.ofNat ⟨𝓜.ofNat_injective, 𝓜.ofNat_surjective⟩
  on_func
  | .zero, v => by simp [Vec.eq_nil]; rfl
  | .succ, v => by rw [Vec.eq_one (_ ∘ _)]; rfl
  | .add, v => by rw [Vec.eq_two (_ ∘ _)]; apply 𝓜.ofNat_add
  | .mul, v => by rw [Vec.eq_two (_ ∘ _)]; apply 𝓜.ofNat_mul
  on_rel r := nomatch r

noncomputable def categoricity : PA.Categorical
| 𝓜₁, 𝓜₂ => .trans (.symm (model_iso_𝓝 𝓜₁)) (model_iso_𝓝 𝓜₂)

end SecondOrder.Language.Theory.PA
