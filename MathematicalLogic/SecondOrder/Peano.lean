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

inductive PA₂ : Peano.Theory where
| succ_ne_zero : PA₂ (∀' (~ S #0 ≐ 0))
| succ_inj : PA₂ (∀' (∀' (S #1 ≐ S #0 ⇒ #1 ≐ #0)))
| add_zero : PA₂ (∀' (#0 + 0 ≐ #0))
| add_succ : PA₂ (∀' (∀' (#1 + S #0 ≐ S (#1 + #0))))
| mul_zero : PA₂ (∀' (#0 * 0 ≐ 0))
| mul_succ : PA₂ (∀' (∀' (#1 * S #0 ≐ #1 * #0 + #1)))
| ind : PA₂ (∀ʳ 1 (0 ⬝ʳᵛ [0]ᵥ ⇒ (∀' (1 ⬝ʳᵛ [#0]ᵥ ⇒ 1 ⬝ʳᵛ [S #0]ᵥ)) ⇒ ∀' (1 ⬝ʳᵛ [#0]ᵥ)))


namespace PA₂

attribute [local simp] Structure.satisfy Structure.interpFormula Structure.interpTerm Structure.Assignment.cons
  Vec.eq_two Vec.eq_one Vec.eq_nil

def 𝓝 : PA₂.Model where
  Dom := ℕ
  interpFunc
  | .zero, _ => 0
  | .succ, v => (v 0).succ
  | .add, v => v 0 + v 1
  | .mul, v => v 0 * v 1
  interpRel r := nomatch r
  satisfy_theory p h := by
    cases h with simp
    | add_succ => intro n m; rfl
    | mul_succ => intro n m; rfl
    | ind =>
      intros r h₁ h₂ n
      induction n with
      | zero => exact h₁
      | succ n ih => exact h₂ _ ih

variable {𝓜 : PA₂.Model}

instance : Zero 𝓜 := ⟨𝓜.interpFunc .zero []ᵥ⟩
instance : Add 𝓜 := ⟨(𝓜.interpFunc .add [·, ·]ᵥ)⟩
instance : Mul 𝓜 := ⟨(𝓜.interpFunc .mul [·, ·]ᵥ)⟩

def succ (u : 𝓜) := 𝓜.interpFunc .succ [u]ᵥ
def ofNat : ℕ → 𝓜
| 0 => 0
| n + 1 => succ (ofNat n)

theorem ofNat_injective : Function.Injective (@ofNat 𝓜) := by
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
    have := 𝓜.satisfy_theory _ .succ_ne_zero
    simp at this; apply this; symm; exact h₁
  | succ n ih =>
    have := 𝓜.satisfy_theory _ .succ_inj
    simp at this; apply this at h₁
    cases' m with m <;> simp at h₃
    exact ih _ h₁ h₃

theorem ofNat_surjective : Function.Surjective (@ofNat 𝓜) := by
  intro u
  have := 𝓜.satisfy_theory _ .ind
  simp at this
  apply this (r := λ v => ∃ n, ofNat n = v 0)
  · exists 0
  · intro u ⟨n, h₁⟩
    exists n.succ
    rw [ofNat, h₁]
    rfl

theorem ofNat_add : @ofNat 𝓜 (n + m) = ofNat n + ofNat m := by
  symm
  induction m with
  | zero =>
    have := 𝓜.satisfy_theory _ .add_zero
    simp at this; apply this
  | succ m ih =>
    have := 𝓜.satisfy_theory _ .add_succ
    simp at this
    trans
    · apply this
    · simp_rw [Nat.add_succ, ofNat, ←ih]; rfl

theorem ofNat_mul : @ofNat 𝓜 (n * m) = ofNat n * ofNat m := by
  symm
  induction m with
  | zero =>
    have := 𝓜.satisfy_theory _ .mul_zero
    simp at this; apply this
  | succ m ih =>
    have := 𝓜.satisfy_theory _ .mul_succ
    simp at this
    trans
    · apply this
    · simp [Nat.mul_succ, ofNat_add, ←ih]; rfl

noncomputable def model_iso_𝓝 (𝓜 : PA₂.Model) : 𝓝 ≃ᴹ 𝓜.toStructure where
  toEquiv := Equiv.ofBijective ofNat ⟨ofNat_injective, ofNat_surjective⟩
  on_func
  | .zero, v => by simp [Vec.eq_nil]; rfl
  | .succ, v => by rw [Vec.eq_one (_ ∘ _)]; rfl
  | .add, v => by rw [Vec.eq_two (_ ∘ _)]; apply ofNat_add
  | .mul, v => by rw [Vec.eq_two (_ ∘ _)]; apply ofNat_mul
  on_rel r := nomatch r

noncomputable def categorical : PA₂.Categorical
| 𝓜₁, 𝓜₂ => .trans (.symm (model_iso_𝓝 𝓜₁)) (model_iso_𝓝 𝓜₂)

end SecondOrder.Language.Theory.PA₂
