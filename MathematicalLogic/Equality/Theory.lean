import MathematicalLogic.FirstOrder.Theory

class EqLanguage (𝓛 : Language) where
  eq : 𝓛.𝓟 2

variable [EqLanguage 𝓛]

def Term.eq (t₁ t₂ : Term 𝓛) := EqLanguage.eq ⬝ₚ (t₁ ∷ₜ t₂ ∷ₜ []ₜ)
infix:60 " ≈ " => Term.eq

def Term.neq (t₁ t₂ : Term 𝓛) := ~ t₁ ≈ t₂
infix:60 " ≉ " => Term.neq

def Terms.eq : Terms 𝓛 n → Terms 𝓛 n → Formula 𝓛
| []ₜ, []ₜ => ⊤
| t ∷ₜ ts, t' ∷ₜ ts' => (t ≈ t') ⋀ ts.eq ts'
infix:60 " ≋ " => Terms.eq

def Formula.exists_unique (p : Formula 𝓛) :=
  ∃' (p ⋀ ∀' (↑ₚp ⟶ #1 ≈ (#0 : Term 𝓛)))

prefix:max "∃'! " => Formula.exists_unique

def BTerm.eq (t₁ t₂ : BTerm 𝓛 m) : BFormula 𝓛 m :=
  EqLanguage.eq ⬝ₚ (t₁ ∷ₜ t₂ ∷ₜ []ₜ)
infix:60 " ≈ " => BTerm.eq

def BTerm.neq (t₁ t₂ : BTerm 𝓛 m) : BFormula 𝓛 m := ~ t₁ ≈ t₂
infix:60 " ≉ " => BTerm.neq

def BTerms.eq : BTerms 𝓛 m n → BTerms 𝓛 m n → BFormula 𝓛 m
| []ₜ, []ₜ => ⊤
| t ∷ₜ ts, t' ∷ₜ ts' => (t ≈ t') ⋀ ts.eq ts'
infix:60 " ≋ " => BTerms.eq

def BFormula.exists_unique (p : BFormula 𝓛 (m + 1)) :=
  ∃ᵇ (p ⋀ ∀ᵇ (↑ₚp ⟶ #'1 ≈ (#'0 : BTerm 𝓛 (m + 2))))
prefix:max "∃ᵇ! " => BFormula.exists_unique

@[simp] theorem Term.subst_eq {t₁ t₂ : Term 𝓛} : (t₁ ≈ t₂)[σ]ₚ = t₁[σ]ₜ ≈ t₂[σ]ₜ := by simp [Term.eq]
@[simp] theorem Term.subst_neq {t₁ t₂ : Term 𝓛} : (t₁ ≉ t₂)[σ]ₚ = t₁[σ]ₜ ≉ t₂[σ]ₜ := by simp [Term.neq]

@[simp] theorem BTerm.unbounded_eq {t₁ t₂ : BTerm 𝓛 m} : (t₁ ≈ t₂).unbounded = t₁.unbounded ≈ t₂.unbounded := by simp [BTerm.eq, Term.eq]
@[simp] theorem BTerm.unbounded_neq {t₁ t₂ : BTerm 𝓛 m} : (t₁ ≉ t₂).unbounded = t₁.unbounded ≉ t₂.unbounded := by simp [BTerm.neq, Term.neq]

@[simp] theorem BTerm.subst_eq {t₁ t₂ : BTerm 𝓛 m} {σ : BSubst 𝓛 m k} : (t₁ ≈ t₂)[σ]ₚ = t₁[σ]ₜ ≈ t₂[σ]ₜ := by simp [BTerm.eq]
@[simp] theorem BTerm.subst_neq {t₁ t₂ : BTerm 𝓛 m} {σ : BSubst 𝓛 m k} : (t₁ ≉ t₂)[σ]ₚ = t₁[σ]ₜ ≉ t₂[σ]ₜ := by simp [BTerm.neq]

inductive EQ : Theory 𝓛 where
| e1 : EQ (∀ᵇ (#'0 ≈ #'0))
| e2 : EQ (∀* ((t₁ ≈ t₂) ⟶ p[↦ₛ t₁]ₚ ⟶ p[↦ₛ t₂]ₚ))

class EqTheory (𝓣 : Theory 𝓛) where
  eqAxioms : EQ ⊆ 𝓣

instance : EqTheory (EQ : Theory 𝓛) := ⟨Set.Subset.refl _⟩

namespace Proof

variable {𝓣 : Theory 𝓛} [EqTheory 𝓣]

theorem refl {t : Term 𝓛} : 𝓣 ⊢ t ≈ t := by
  have h : 𝓣 ⊢ (∀ᵇ (#'0 ≈ #'0) : BFormula 𝓛 0)
  · apply Theory.axioms
    apply EqTheory.eqAxioms
    apply EQ.e1
  simp at h
  apply Proof.mp (Proof.forall_elim (t := t)) at h
  simp [Subst.single] at h
  exact h

macro "prefl" : tactic => `(tactic| (pweaken; exact refl))

theorem refl_terms {ts : Terms 𝓛 n} : 𝓣 ⊢ ts ≋ ts :=
  match ts with
  | []ₜ => Proof.true_intro
  | t ∷ₜ ts => by
    apply Proof.mp2 Proof.and_intro
    · prefl
    · apply refl_terms

theorem subst {t₁ t₂ : Term 𝓛} {p : Formula 𝓛} :
  𝓣 ⊢ t₁ ≈ t₂ ⟶ p[↦ₛ t₁]ₚ ⟶ p[↦ₛ t₂]ₚ := by
  let m := max p.bound (max t₁.bound t₂.bound)
  let t₁' := t₁.bounded (m := m) (by simp)
  let t₂' := t₂.bounded (m := m) (by simp)
  let p' := p.bounded (m := m + 1) (by simp [Nat.le_succ_of_le])
  have h : 𝓣 ⊢ ∀* ((t₁' ≈ t₂') ⟶ p'[↦ₛ t₁']ₚ ⟶ p'[↦ₛ t₂']ₚ)
  · apply Theory.axioms
    apply EqTheory.eqAxioms
    apply EQ.e2
  apply Proof.mp Sentence.foralls_elim_self at h
  simp [Term.bounded_unbounded, Formula.bounded_subst_single_unbounded] at h
  exact h

theorem symm {t₁ t₂ : Term 𝓛} :
  𝓣 ⊢ t₁ ≈ t₂ ⟶ t₂ ≈ t₁ := by
  pintro
  have h := subst (𝓣 := 𝓣) (t₁ := t₁) (t₂ := t₂) (p := #0 ≈ ↑ₜt₁)
  simp [Term.shift_subst_single] at h
  apply Proof.mp2 (Proof.weaken_add h)
  · passumption
  · prefl

macro "psymm" : tactic => `(tactic| (apply Proof.mp; pweaken; exact symm))

theorem symm_terms {ts₁ ts₂ : Terms 𝓛 n} :
  𝓣 ⊢ ts₁ ≋ ts₂ ⟶ ts₂ ≋ ts₁ :=
  match ts₁, ts₂ with
  | []ₜ, []ₜ => Proof.identity
  | t₁ ∷ₜ ts₁, t₂ ∷ₜ ts₂ => by
    pintro
    apply Proof.mp2 Proof.and_intro
    · psymm
      apply Proof.mp Proof.and_left
      passumption
    · apply Proof.mp (Proof.weaken_add symm_terms)
      apply Proof.mp Proof.and_right
      passumption

theorem trans {t₁ t₂ t₃ : Term 𝓛} :
  𝓣 ⊢ t₁ ≈ t₂ ⟶ t₂ ≈ t₃ ⟶ t₁ ≈ t₃ := by
  pintro
  have h := subst (𝓣 := 𝓣) (t₁ := t₂) (t₂ := t₁) (p := #0 ≈ ↑ₜt₃)
  simp [Term.shift_subst_single] at h
  apply Proof.mp (Proof.weaken_add h)
  psymm
  passumption

macro "ptrans" t:term : tactic => `(tactic| (apply Proof.mp2; pweaken; exact trans (t₂ := $t)))

theorem subst_iff {t₁ t₂ : Term 𝓛} {p : Formula 𝓛} :
  𝓣 ⊢ t₁ ≈ t₂ ⟶ (p[↦ₛ t₁]ₚ ⟷ p[↦ₛ t₂]ₚ) := by
  pintro
  apply Proof.mp2 Proof.iff_intro <;> apply Proof.mp (Proof.weaken_add subst)
  · passumption
  · psymm; passumption

theorem subst_term {t t₁ t₂ : Term 𝓛} :
  𝓣 ⊢ t₁ ≈ t₂ ⟶ t[↦ₛ t₁]ₜ ≈ t[↦ₛ t₂]ₜ := by
  pintro
  have h := subst (𝓣 := 𝓣) (t₁ := t₁) (t₂ := t₂) (p := ↑ₜ(t[↦ₛ t₁]ₜ) ≈ t)
  simp [Term.shift_subst_single] at h
  apply Proof.mp2 (Proof.weaken_add h)
  · passumption
  · prefl

lemma cast_func {f : 𝓛.𝓕 n} {ts₁ : Terms 𝓛 n} {ts₂ : Terms 𝓛 m} (h : n = m) :
  HEq ts₁ ts₂ → f ⬝ₜ ts₁ = (cast (by rw [h]) f) ⬝ₜ ts₂ := by
  intro h
  congr
  symm
  apply cast_heq

lemma congr_func_aux
  {f : 𝓛.𝓕 (n + m)} {ts₁ ts₂ : Terms 𝓛 n} {ts : Terms 𝓛 m} :
  𝓣 ⊢ ts₁ ≋ ts₂ ⟶ f ⬝ₜ (ts ++ ts₁) ≈ f ⬝ₜ (ts ++ ts₂) :=
  match n, ts₁, ts₂ with
  | 0, []ₜ, []ₜ => by pintro; prefl
  | n + 1, t₁ ∷ₜ ts₁, t₂ ∷ₜ ts₂ => by
    pintro
    ptrans f ⬝ₜ (ts ++ t₂ ∷ₜ ts₁)
    · have h := subst_term (𝓣 := 𝓣) (t₁ := t₁) (t₂ := t₂) (t := f ⬝ₜ (↑ₜₛts ++ #0 ∷ₜ ↑ₜₛts₁))
      simp [Terms.subst_append, Terms.shift_subst_single] at h
      apply Proof.mp (Proof.weaken_add h)
      apply Proof.mp Proof.and_left
      passumption
    · have h : n + 1 + m = n + (0 + 1 + m)
      · simp [Nat.zero_add, Nat.add_assoc]
      simp [cast_func h Terms.append_cons]
      apply Proof.mp (Proof.weaken_add congr_func_aux)
      apply Proof.mp Proof.and_right
      passumption

theorem congr_func {f : 𝓛.𝓕 n} {ts₁ ts₂ : Terms 𝓛 n} :
  𝓣 ⊢ ts₁ ≋ ts₂ ⟶ f ⬝ₜ ts₁ ≈ f ⬝ₜ ts₂ :=
  congr_func_aux (ts := []ₜ)

lemma cast_atom {p : 𝓛.𝓟 n} {ts₁ : Terms 𝓛 n} {ts₂ : Terms 𝓛 m} (h : n = m) :
  HEq ts₁ ts₂ → p ⬝ₚ ts₁ = (cast (by rw [h]) p) ⬝ₚ ts₂ := by
  intro h
  congr
  symm
  apply cast_heq

lemma congr_atom_aux
  {p : 𝓛.𝓟 (n + m)} {ts₁ ts₂ : Terms 𝓛 n} {ts : Terms 𝓛 m} :
  𝓣 ⊢ ts₁ ≋ ts₂ ⟶ p ⬝ₚ (ts ++ ts₁) ⟶ p ⬝ₚ (ts ++ ts₂) :=
  match n, ts₁, ts₂ with
  | 0, []ₜ, []ₜ => by pintro; exact Proof.identity
  | n + 1, t₁ ∷ₜ ts₁, t₂ ∷ₜ ts₂ => by
    pintro
    apply Proof.mp2 Proof.composition
    · have h := subst (𝓣 := 𝓣) (t₁ := t₁) (t₂ := t₂) (p := p ⬝ₚ (↑ₜₛts ++ #0 ∷ₜ ↑ₜₛts₁))
      simp [Terms.subst_append, Terms.shift_subst_single] at h
      apply Proof.mp (Proof.weaken_add h)
      apply Proof.mp Proof.and_left
      passumption
    · have h : n + 1 + m = n + (0 + 1 + m)
      · simp [Nat.zero_add, Nat.add_assoc]
      simp [cast_atom h Terms.append_cons]
      apply Proof.mp (Proof.weaken_add congr_atom_aux)
      apply Proof.mp Proof.and_right
      passumption

theorem congr_atom {p : 𝓛.𝓟 n} {ts₁ ts₂ : Terms 𝓛 n} :
  𝓣 ⊢ ts₁ ≋ ts₂ ⟶ p ⬝ₚ ts₁ ⟶ p ⬝ₚ ts₂ :=
  congr_atom_aux (ts := []ₜ)

theorem congr_atom_iff {p : 𝓛.𝓟 n} {ts₁ ts₂ : Terms 𝓛 n} :
  𝓣 ⊢ ts₁ ≋ ts₂ ⟶ (p ⬝ₚ ts₁ ⟷ p ⬝ₚ ts₂) := by
  pintro
  apply Proof.mp2 Proof.iff_intro <;> apply Proof.mp (Proof.weaken_add congr_atom)
  · passumption
  · apply Proof.mp (Proof.weaken_add symm_terms)
    passumption

end Proof
