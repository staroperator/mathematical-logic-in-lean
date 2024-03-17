import Mathlib.Tactic.Linarith
import MathematicalLogic.Equality.Theory

namespace Model

variable [EqLanguage 𝓛] {𝓣 : Theory 𝓛} [EqTheory 𝓣] {𝓜 : Model 𝓣}
  {u₁ u₂ u₃ : 𝓜.𝓤} {v₁ v₂ v₃ : Vector 𝓜.𝓤 n}

def eq (𝓜 : Model 𝓣) (u₁ u₂ : 𝓜.𝓤) := 𝓜.𝓟 EqLanguage.eq (u₁ ∷ᵥ u₂ ∷ᵥ []ᵥ)

instance : HasEquiv 𝓜.𝓤 := ⟨𝓜.eq⟩

theorem eq_refl : u₁ ≈ u₁ := by
  have h := Proof.refl (𝓣 := 𝓣) (t := #0)
  apply Theory.soundness (ρ := λ _ => u₁) at h
  exact h

theorem eq_symm : u₁ ≈ u₂ → u₂ ≈ u₁ := by
  intro h₁
  have h := Proof.symm (𝓣 := 𝓣) (t₁ := #0) (t₂ := #1)
  let ρ := λ | 0 => u₁ | _ => u₂
  apply Theory.soundness (ρ := ρ) at h
  exact h h₁

theorem eq_trans : u₁ ≈ u₂ → u₂ ≈ u₃ → u₁ ≈ u₃ := by
  intros h₁ h₂
  have h := Proof.trans (𝓣 := 𝓣) (t₁ := #0) (t₂ := #1) (t₃ := #2)
  let ρ := λ | 0 => u₁ | 1 => u₂ | _ => u₃
  apply Theory.soundness (ρ := ρ) at h
  exact h h₁ h₂

def eqv (𝓜 : Model 𝓣) : ∀ {n}, Vector 𝓜.𝓤 n → Vector 𝓜.𝓤 n → Prop
| 0, ⟨[], _⟩, ⟨[], _⟩ => True
| _ + 1, ⟨u₁ :: l₁, h₁⟩, ⟨u₂ :: l₂, h₂⟩ =>
  u₁ ≈ u₂ ∧ 𝓜.eqv ⟨l₁, Nat.succ.inj h₁⟩ ⟨l₂, Nat.succ.inj h₂⟩

instance : HasEquiv (Vector 𝓜.𝓤 n) := ⟨𝓜.eqv⟩

@[simp] theorem eqv_cons : 𝓜.eqv (u₁ ∷ᵥ v₁) (u₂ ∷ᵥ v₂) = (u₁ ≈ u₂ ∧ 𝓜.eqv v₁ v₂) := rfl

theorem eqv_refl : v₁ ≈ v₁ :=
  Vector.inductionOn v₁ True.intro (λ ih => ⟨eq_refl, ih⟩)

theorem eqv_symm : v₁ ≈ v₂ → v₂ ≈ v₁ :=
  Vector.inductionOn₂ v₁ v₂
    (λ _ => True.intro)
    (λ ih ⟨h, h'⟩ => ⟨eq_symm h, ih h'⟩)

theorem eqv_trans : v₁ ≈ v₂ → v₂ ≈ v₃ → v₁ ≈ v₃ :=
  Vector.inductionOn₃ v₁ v₂ v₃
    (λ _ _ => True.intro)
    (λ ih ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ => ⟨eq_trans h₁ h₂, ih h₁' h₂'⟩)

instance setoid : Setoid 𝓜.𝓤 :=
  ⟨𝓜.eq, ⟨λ _ => eq_refl, eq_symm, eq_trans⟩⟩
instance setoidVec (n) : Setoid (Vector 𝓜.𝓤 n) :=
  ⟨𝓜.eqv, ⟨λ _ => eqv_refl, eqv_symm, eqv_trans⟩⟩

lemma eqv_interp {n} {ts₁ ts₂ : Terms 𝓛 n} :
  ⟦ ts₁ ≋ ts₂ ⟧ₚ 𝓜, ρ = 𝓜.eqv (⟦ ts₁ ⟧ₜₛ 𝓜, ρ) (⟦ ts₂ ⟧ₜₛ 𝓜, ρ) :=
  match ts₁, ts₂ with
  | []ₜ, []ₜ => by simp; exact True.intro
  | t₁ ∷ₜ ts₁, t₂ ∷ₜ ts₂ => by
    simp only [Terms.eq, Formula.interp_and, Terms.interp, eqv_cons]
    congr
    · simp; rfl
    · exact eqv_interp

theorem eq_congr_func : v₁ ≈ v₂ → 𝓜.𝓕 f v₁ ≈ 𝓜.𝓕 f v₂ := by
  intro h₁
  have h := Proof.congr_func (𝓣 := 𝓣) (f := f)
    (ts₁ := Terms.ofVector $ Vector.ofFn (λ x => #x))
    (ts₂ := Terms.ofVector $ Vector.ofFn (λ x => #(n + x)))
  let ρ := λ x =>
    if h₁ : x < n then v₁.get ⟨x, h₁⟩
    else if h₂ : x < n + n then v₂.get ⟨x - n, by
      simp at h₁
      apply lt_of_add_lt_add_right
      rw [Nat.sub_add_cancel h₁]
      exact h₂⟩
    else default
  apply Theory.soundness (ρ := ρ) at h
  simp [Terms.interp_of_vector, ρ] at h
  apply h
  rw [eqv_interp]
  simp [Terms.interp_of_vector]
  exact h₁

theorem eq_congr_atom : v₁ ≈ v₂ → (𝓜.𝓟 p v₁ ↔ 𝓜.𝓟 p v₂) := by
  intro h₁
  have h := Proof.congr_atom_iff (𝓣 := 𝓣) (p := p)
    (ts₁ := Terms.ofVector $ Vector.ofFn (λ x => #x))
    (ts₂ := Terms.ofVector $ Vector.ofFn (λ x => #(n + x)))
  let ρ := λ x =>
    if h₁ : x < n then v₁.get ⟨x, h₁⟩
    else if h₂ : x < n + n then v₂.get ⟨x - n, by
      simp at h₁
      apply lt_of_add_lt_add_right
      rw [Nat.sub_add_cancel h₁]
      exact h₂⟩
    else default
  apply Theory.soundness (ρ := ρ) at h
  simp only [Formula.interp_imp, Formula.interp_iff] at h
  simp [Terms.interp_of_vector, ρ] at h
  apply h
  rw [eqv_interp]
  simp [Terms.interp_of_vector]
  exact h₁

def liftVec (𝓜 : Model 𝓣) (v : Vector (Quotient 𝓜.setoid) n) : Quotient (𝓜.setoidVec n) :=
  v.inductionOn ⟦[]ᵥ⟧
    (@λ n u _ v =>
      Quotient.liftOn₂ u v
        (λ u v => ⟦u ∷ᵥ v⟧)
        (by intros _ _ _ _ h₁ h₂; simp; exact ⟨h₁, h₂⟩))

@[simp] lemma lift_vec_cons
  {𝓜 : Model 𝓣} {u : Quotient 𝓜.setoid} {v : Vector (Quotient 𝓜.setoid) n} :
  𝓜.liftVec (u ∷ᵥ v) = (
    Quotient.liftOn₂ u (𝓜.liftVec v)
      (λ u v => ⟦u ∷ᵥ v⟧)
      (by intros _ _ _ _ h₁ h₂; simp; exact ⟨h₁, h₂⟩)) := rfl

def quotientStructure (𝓜 : Model 𝓣) : Structure 𝓛 where
  𝓤 := Quotient 𝓜.setoid
  inhabited := inferInstance
  𝓕 := λ f v =>
    Quotient.liftOn (𝓜.liftVec v)
      (λ v => ⟦𝓜.𝓕 f v⟧)
      (by intros _ _ h; simp [eq_congr_func h])
  𝓟 := λ p v =>
    Quotient.liftOn (𝓜.liftVec v)
      (λ v => 𝓜.𝓟 p v)
      (by intros _ _ h; simp [eq_congr_atom h])

mutual
lemma Term.interp_quotient_structure
  {t : Term 𝓛} {ρ : Assignment 𝓜.val} :
  ⟦ t ⟧ₜ 𝓜.quotientStructure, (λ x => ⟦ρ x⟧) = ⟦ ⟦ t ⟧ₜ 𝓜, ρ ⟧ :=
  match t with
  | #x => by simp
  | f ⬝ₜ ts => by
    unfold quotientStructure
    simp
    have h := Terms.interp_quotient_structure (ts := ts) (ρ := ρ)
    unfold quotientStructure at h
    simp [h]
lemma Terms.interp_quotient_structure
  {n} {ts : Terms 𝓛 n} {ρ : Assignment 𝓜.val} :
  𝓜.liftVec (⟦ ts ⟧ₜₛ 𝓜.quotientStructure, (λ x => ⟦ρ x⟧)) = ⟦ ⟦ ts ⟧ₜₛ 𝓜, ρ ⟧ :=
  match ts with
  | []ₜ => rfl
  | t ∷ₜ ts => by
    simp
    rw [lift_vec_cons, Term.interp_quotient_structure, Terms.interp_quotient_structure]
    simp
end

lemma Formula.interp_quotient_structure
  {p : Formula 𝓛} {ρ : Assignment 𝓜.val} :
  ⟦ p ⟧ₚ 𝓜.quotientStructure, (λ x => ⟦ρ x⟧) ↔ ⟦ p ⟧ₚ 𝓜, ρ := by
  induction p generalizing ρ <;> simp
  case atom p ts =>
    unfold quotientStructure
    simp
    have h := Terms.interp_quotient_structure (ts := ts) (ρ := ρ)
    unfold quotientStructure at h
    simp [h]
  case imp _ _ ih₁ ih₂ =>
    simp [ih₁, ih₂]
  case all _ ih =>
    have h {u} : (λ x => ⟦(u ∷ₐ ρ) x⟧) = Assignment.cons (𝓜 := 𝓜.quotientStructure) ⟦u⟧ (λ (x : ℕ) => ⟦ρ x⟧) := by
      funext x; cases x <;> rfl
    simp [←ih, h]
    constructor
    · intros h u
      exact h ⟦u⟧
    · intros h u
      rcases Quotient.exists_rep u with ⟨u, h'⟩
      subst h'
      exact h u

def quotientModel (𝓜 : Model 𝓣) : Model 𝓣 where
  val := 𝓜.quotientStructure
  property := by
   intros p h
   let ρ : Assignment 𝓜.val := default
   rw [Sentence.unbounded_interp_eq (𝓜 := 𝓜.quotientStructure) (ρ := λ x => ⟦ρ x⟧)]
   rw [Formula.interp_quotient_structure]
   rw [←Sentence.unbounded_interp_eq]
   apply 𝓜.property
   exact h

theorem quotient_model_interp_eq {u₁ u₂ : 𝓜.quotientModel.𝓤} :
  u₁ ≈ u₂ ↔ u₁ = u₂ := by
  constructor
  · intro h
    rcases Quotient.exists_rep u₁ with ⟨u₁, h₁⟩
    rcases Quotient.exists_rep u₂ with ⟨u₂, h₂⟩
    subst h₁ h₂
    apply Quotient.sound
    exact h
  · intro h
    rw [h]
    apply eq_refl

end Model
