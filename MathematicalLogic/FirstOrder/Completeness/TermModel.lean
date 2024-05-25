import MathematicalLogic.FirstOrder.Semantics
import MathematicalLogic.FirstOrder.Completeness.Defs

def Vec.setoid (s : Setoid α) (n : ℕ) : Setoid (Vec α n) where
  r v₁ v₂ := ∀ i, s.r (v₁ i) (v₂ i)
  iseqv.refl _ _ := s.iseqv.refl _
  iseqv.symm h i := s.iseqv.symm (h i)
  iseqv.trans h₁ h₂ i := s.iseqv.trans (h₁ i) (h₂ i)

instance [s : Setoid α] : Setoid (Vec α n) := Vec.setoid s n

def Vec.quotient {s : Setoid α} (v : Vec (Quotient s) n) : Quotient (Vec.setoid s n) :=
  v.rec ⟦[]ᵥ⟧
    (λ a _ v => Quotient.liftOn₂ a v (⟦· ∷ᵥ ·⟧)
      (by
        intros; simp; intro i
        cases i using Fin.cases with
        | zero => assumption
        | succ => apply_assumption))

theorem Vec.quotient_mk :
  quotient (s := s) (λ i => ⟦v i⟧) = ⟦v⟧ := by
  induction v using Vec.rec with
  | nil => simp [Vec.eq_nil, quotient]
  | cons a v ih =>
    rw [Vec.eq_cons λ _ => _]
    simp [head, tail, Function.comp, quotient]
    rw [←quotient]
    simp [ih]

def Quotient.liftOnVec
  {s : Setoid α}
  (v : Vec (Quotient s) n)
  (f : Vec α n → β)
  (c : (v₁ v₂ : Vec α n) → v₁ ≈ v₂ → f v₁ = f v₂) : β :=
  Quotient.liftOn v.quotient f c

theorem Quotient.liftOnVec_mk
  {s : Setoid α} {f : Vec α n → β} {c : (v₁ v₂ : Vec α n) → v₁ ≈ v₂ → f v₁ = f v₂} :
  liftOnVec (λ i => ⟦v i⟧) f c = f v := by
  simp [liftOnVec, Vec.quotient_mk, Quotient.liftOn_mk]



namespace FirstOrder.Language

variable {𝓛 : Language}

namespace Context

variable (Γ : 𝓛.Context)

def TermSetoid : Setoid 𝓛.Term where
  r p q := Γ ⊢ p ≐ q
  iseqv.refl _ := Proof.refl
  iseqv.symm := Proof.symm.mp
  iseqv.trans := Proof.trans.mp2

@[simps] def TermModel (Γ : 𝓛.Context) : 𝓛.Structure where
  𝓤 := Quotient Γ.TermSetoid
  inhabited𝓤 := ⟨⟦#0⟧⟩
  interp𝓕 f v :=
    Quotient.liftOnVec v (⟦f ⬝ₜ ·⟧)
      (by intros v₁ v₂ h; simp; papply Proof.congr_func; exact Proof.andN_intro h)
  interp𝓡 r v :=
    Quotient.liftOnVec v (Γ ⊢ r ⬝ᵣ ·)
      (by intros v₁ v₂ h; simp; apply Proof.iff_iff; papply Proof.congr_rel_iff; exact Proof.andN_intro h)

end Context

variable {Γ : 𝓛.Context} {ρ : 𝓛.Subst}

theorem Term.interp_term_model : ⟦ t ⟧ₜ Γ.TermModel, (⟦ρ ·⟧) = ⟦t[ρ]ₜ⟧ := by
  induction t with simp [Term.interp]
  | func f v ih => simp [ih, Quotient.liftOnVec_mk]

lemma subst_const {c : 𝓛.Const} : (c : 𝓛.Term)[σ]ₜ = c := by simp; apply Vec.eq_nil

variable  (h₁ : Γ.Consistent) (h₂ : Γ.Complete) (h₃ : Γ.Saturated)

theorem Formula.interp_term_model :
  (Γ.TermModel ⊨[(⟦ρ ·⟧)] p ↔ Γ ⊢ p[ρ]ₚ) := by
  induction p generalizing ρ with simp [Formula.interp]
  | rel r v => simp [Term.interp_term_model, Quotient.liftOnVec_mk]
  | eq t₁ t₂ => simp [Term.interp_term_model]; rfl
  | false => exact h₁
  | imp p q ih₁ ih₂ =>
    rw [ih₁, ih₂]
    constructor
    · intro h
      rcases h₂ (p[ρ]ₚ) with h' | h'
      · pintro; pexact (h h')
      · papply Proof.contradiction; exact h'
    · exact Proof.mp
  | all p ih =>
    constructor
    · intro h₁'
      rcases h₂ (∀' p[⇑ₛρ]ₚ) with h₂' | h₂'
      · exact h₂'
      · exfalso
        apply Proof.mp Proof.not_forall at h₂'
        apply h₃ at h₂'
        rcases h₂' with ⟨c, h₂'⟩
        simp at h₂'; rw [←subst_const (σ := ρ), ←Formula.subst_swap, ←Formula.subst_comp] at h₂'
        apply h₁
        apply h₂'.mp
        simp [←ih]
        have : (λ x => ⟦(↦ₛ c x)[ρ]ₜ⟧) = Structure.Assignment.cons (𝓢 := Γ.TermModel) ⟦c⟧ (⟦ρ ·⟧) := by
          funext x; cases x <;> simp [Structure.Assignment.cons, Vec.eq_nil]
        rw [this]
        apply h₁'
    · rintro h ⟨t⟩
      apply Proof.mp (Proof.ax (.a4 (t := t))) at h
      rw [←Formula.subst_comp, ←ih] at h
      have : (λ x => ⟦(⇑ₛρ ∘ₛ ↦ₛ t) x⟧) = Structure.Assignment.cons (𝓢 := Γ.TermModel) ⟦t⟧ (⟦ρ ·⟧) := by
        funext x; cases x <;> simp [Structure.Assignment.cons, Term.shift_subst_single]
      rw [this] at h
      exact h

theorem satisfiable_by_term_model : Γ.Satisfiable := by
  apply Context.Satisfiable.up.{0}
  exists Γ.TermModel, (⟦Subst.id ·⟧)
  intros p h
  rw [Formula.interp_term_model h₁ h₂ h₃, Formula.subst_id]
  exact Proof.hyp h

end FirstOrder.Language
