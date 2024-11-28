import MathematicalLogic.FirstOrder.Completeness.Language

lemma Set.decompose_subset_union {s₁ s₂ s₃ : Set α} :
  s₁ ⊆ s₂ ∪ s₃ → ∃ s₄ s₅, s₁ = s₄ ∪ s₅ ∧ s₄ ⊆ s₂ ∧ s₅ ⊆ s₃ := by
  intros h
  exists s₁ ∩ s₂
  exists s₁ ∩ s₃
  aesop

def Fin.embedAt : (k : ℕ) → Fin (n + k + 1)
| 0 => 0
| k + 1 => (embedAt k).succ

def Fin.insertAt : (k : ℕ) → Fin (n + k) → Fin (n + k + 1)
| 0, x => x.succ
| k + 1, x => x.cases 0 λ x => (insertAt k x).succ

theorem Fin.embedAt_or_insertAt (x : Fin (n + k + 1)) : x = embedAt k ∨ ∃ y, x = insertAt k y := by
  induction k with
  | zero =>
    cases x using Fin.cases with
    | zero => left; rfl
    | succ x => right; exists x
  | succ k ih =>
    cases x using Fin.cases with
    | zero => right; exists Fin.ofNat 0
    | succ x =>
      rcases ih x with h | ⟨y, h⟩
      · left; simp [h, embedAt]
      · right; exists y.succ; simp [h, insertAt]

namespace FirstOrder.Language

variable {𝓛 : Language}

def Term.consts : 𝓛.Term n → Set 𝓛.Const
| #_ => {}
| .func (m := 0) c _ => {c}
| .func (m := _ + 1) _ v => ⋃i, (v i).consts

def Formula.consts : 𝓛.Formula n → Set 𝓛.Const
| _ ⬝ʳ v => ⋃i, (v i).consts
| t₁ ≐ t₂ => t₁.consts ∪ t₂.consts
| ⊥ => {}
| p ⇒ q => p.consts ∪ q.consts
| ∀' p => p.consts

lemma Term.consts_of_subst :
  t[σ]ₜ.consts = t.consts ∪ ⋃ x ∈ t.vars, (σ x).consts := by
  induction t with
  | var x => simp [vars, consts]
  | @func n f v ih =>
    cases n with simp [vars, consts]
    | succ => rw [Set.iUnion_comm, ←Set.iUnion_union_distrib]; simp_rw [ih]

lemma Formula.consts_of_subst {σ : 𝓛.Subst n m} :
  p[σ]ₚ.consts = p.consts ∪ ⋃ x ∈ p.free, (σ x).consts := by
  induction p generalizing m with simp_rw [free, consts]
  | rel r v => simp_rw [Set.biUnion_iUnion, ←Set.iUnion_union_distrib, Term.consts_of_subst]
  | eq t₁ t₂ => simp_rw [Set.biUnion_union, Term.consts_of_subst]; aesop
  | false => simp
  | imp p q ih₁ ih₂ => rw [ih₁, ih₂, Set.biUnion_union]; aesop
  | all p ih =>
    ext c; simp [ih]; apply or_congr_right
    constructor
    · rintro ⟨x, h₁, h₂⟩
      cases x using Fin.cases with
      | zero => contradiction
      | succ x =>
        simp [Term.shift, Term.consts_of_subst] at h₂
        rcases h₂ with (h₂ | ⟨_, _, h₃⟩)
        · exists x
        · simp [Term.consts] at h₃
    · rintro ⟨y, ⟨h₁, h₂⟩⟩
      exists y.succ
      constructor
      · exact h₁
      · simp [Term.shift, Term.consts_of_subst]
        left; exact h₂

def Subst.singleAt : (k : ℕ) → (t : 𝓛.Term n) → 𝓛.Subst (n + k + 1) (n + k)
| 0, t => ↦ₛ t
| k + 1, t => ⇑ₛ (singleAt k t)
local infix:55 " ↦ₛ " => Subst.singleAt

theorem Subst.singleAt_const_app_embedAt {c : 𝓛.Const} : (k ↦ₛ (c : 𝓛.Term n)) (Fin.embedAt k) = (c : 𝓛.Term _) := by
  induction k with simp [singleAt, Fin.embedAt]
  | succ k ih => simp [ih, Term.shift, Vec.eq_nil]

theorem Subst.singleAt_app_insertAt : (k ↦ₛ t) (Fin.insertAt k x) = #x := by
  induction k with simp [singleAt, Fin.insertAt]
  | succ k ih => cases x using Fin.cases <;> simp [ih]

def Subst.shiftAt : (k : ℕ) → 𝓛.Subst (n + k) (n + k + 1)
| 0 => shift
| k + 1 => ⇑ₛ (shiftAt k)

theorem Subst.shiftAt_app : shiftAt (𝓛 := 𝓛) k x = #(Fin.insertAt k x) := by
  induction k with simp [shiftAt, Fin.insertAt]
  | succ k ih => cases x using Fin.cases <;> simp [ih]

theorem Subst.shiftAt_comp_singleAt : shiftAt k ∘ₛ (k ↦ₛ t) = id := by
  funext x; simp
  induction k with simp [singleAt, shiftAt]
  | succ k ih => cases x using Fin.cases <;> simp [Term.shift_subst_lift, ih]

def Subst.insertAt : (k : ℕ) → 𝓛.Subst (n + k) m → (t : 𝓛.Term m) → 𝓛.Subst (n + k + 1) m
| 0, σ, t => t ∷ᵥ σ
| k + 1, σ, t => σ.head ∷ᵥ insertAt k σ.tail t

theorem Subst.insertAt_app_embedAt : insertAt k σ t (Fin.embedAt k) = t := by
  induction k with simp [insertAt, Fin.embedAt]
  | succ k ih => simp [ih]

theorem Subst.insertAt_app_insertAt : insertAt k σ t (Fin.insertAt k x) = σ x := by
  induction k with simp [insertAt, Fin.insertAt]
  | succ k ih => cases x using Fin.cases <;> simp [Vec.head, ih]

open Classical in
noncomputable def Term.invConst (k : ℕ) : 𝓛.Term (n + k) → 𝓛.Const → 𝓛.Term (n + k + 1)
| #x, _ => #(Fin.insertAt k x)
| func (m := 0) f _, c => if f = c then #(Fin.embedAt k) else f ⬝ᶠ []ᵥ
| func (m := _ + 1) f v, c => f ⬝ᶠ λ i => (v i).invConst k c

theorem Term.subst_singleAt_invConst {t : 𝓛.Term (n + k + 1)} (h : c ∉ t.consts) :
  (t[k ↦ₛ c]ₜ).invConst k c = t := by
  induction t with simp
  | var x =>
    rcases Fin.embedAt_or_insertAt x with h | ⟨y, h⟩
    · simp [h, Subst.singleAt_const_app_embedAt, Term.invConst]
    · simp [h, Subst.singleAt_app_insertAt, Term.invConst]
  | @func m f v ih =>
    cases m <;> simp [invConst] <;> simp [Term.consts] at h
    · simp [Ne.symm h, Vec.eq_nil]
    · ext i; simp [ih i (h i)]

theorem Term.invConst_eq_shiftAt {t : 𝓛.Term (n + k)} (h : c ∉ t.consts) :
  t.invConst k c = t[Subst.shiftAt k]ₜ := by
  induction t with
  | var x => simp [invConst, Subst.shiftAt_app]
  | @func m f v ih =>
    cases m <;> simp [invConst] <;> simp [consts] at h
    · simp [Ne.symm h, Vec.eq_nil]
    · ext i; simp [ih i (h i)]

theorem Term.invConst_subst {t : 𝓛.Term (n + k)} {σ : 𝓛.Subst (n + k) (n' + k')} :
  (t[σ]ₜ).invConst k' c = (t.invConst k c)[Subst.insertAt k ((·.invConst k' c) ∘ σ) #(Fin.embedAt k')]ₜ := by
  induction t with
  | var x => simp [invConst, Function.comp, Subst.insertAt_app_insertAt]
  | @func m f v ih =>
    cases m <;> simp [invConst]
    · by_cases h : f = c <;> simp [h, Vec.eq_nil, Subst.insertAt_app_embedAt]
    · simp [ih]

theorem Term.invConst_shift {t : 𝓛.Term (n + k)} :
  (↑ₜt).invConst (k + 1) c = ↑ₜ(t.invConst k c) := by
  rw [shift, invConst_subst]
  congr; funext x; simp [Function.comp, invConst, Fin.embedAt]
  rcases Fin.embedAt_or_insertAt x with h | ⟨y, h⟩
  · simp [h, Subst.insertAt_app_embedAt]
  · simp [h, Subst.insertAt_app_insertAt, invConst, Fin.insertAt]

noncomputable def Formula.invConst (k : ℕ) : 𝓛.Formula (n + k) → 𝓛.Const → 𝓛.Formula (n + k + 1)
| r ⬝ʳ v, c => r ⬝ʳ λ i => (v i).invConst k c
| t₁ ≐ t₂, c => t₁.invConst k c ≐ t₂.invConst k c
| ⊥, _ => ⊥
| p ⇒ q, c => p.invConst k c ⇒ q.invConst k c
| ∀' p, c => ∀' (p.invConst (k + 1) c)
@[simp] theorem Formula.invConst_false : (⊥ : 𝓛.Formula (n + k)).invConst k c = ⊥ := by
  rw [←false_eq]; simp only [invConst]
@[simp] theorem Formula.invConst_imp : (p ⇒ q : 𝓛.Formula (n + k)).invConst k c = p.invConst k c ⇒ q.invConst k c := by
  rw [←imp_eq]; simp only [invConst]
@[simp] theorem Formula.invConst_neg : (~ p : 𝓛.Formula (n + k)).invConst k c = ~ p.invConst k c := by
  rw [←neg_eq, invConst_imp, invConst_false]; rfl

theorem Formula.invConst_andN {v : Vec (𝓛.Formula (n + k)) m} : invConst k (⋀ i, v i) c = ⋀ i, invConst k (v i) c := by
  induction m with simp [andN]
  | zero => simp [Top.top]
  | succ m ih => simp [PropNotation.and, Vec.head, Vec.tail, Function.comp_def, ih]

theorem Formula.subst_singleAt_invConst {p : 𝓛.Formula (n + k + 1)} (h : c ∉ p.consts) :
  (p[k ↦ₛ c]ₚ).invConst k c = p := by
  cases p with (simp [invConst] <;> simp [consts] at h)
  | rel r v => ext i; simp [Term.subst_singleAt_invConst (h i)]
  | eq t₁ t₂ => simp [Term.subst_singleAt_invConst h.left, Term.subst_singleAt_invConst h.right]
  | imp p q => simp [subst_singleAt_invConst h.left, subst_singleAt_invConst h.right]
  | all p => rw [←Subst.singleAt, subst_singleAt_invConst (k := k + 1) h]

theorem Formula.invConst_eq_shiftAt {p : 𝓛.Formula (n + k)} (h : c ∉ p.consts) :
  p.invConst k c = p[Subst.shiftAt k]ₚ := by
  cases p with (simp [invConst] <;> simp [consts] at h)
  | rel r v => ext i; simp [Term.invConst_eq_shiftAt (h i)]
  | eq t₁ t₂ => simp [Term.invConst_eq_shiftAt h.left, Term.invConst_eq_shiftAt h.right]
  | imp p q => simp [invConst_eq_shiftAt h.left, invConst_eq_shiftAt h.right]
  | all p => simp [invConst_eq_shiftAt (k := k + 1) h, Subst.shiftAt]

theorem Formula.invConst_subst {p : 𝓛.Formula (n + k)} {σ : 𝓛.Subst (n + k) (n' + k')} :
  (p[σ]ₚ).invConst k' c = (p.invConst k c)[Subst.insertAt k ((·.invConst k' c) ∘ σ) #(Fin.embedAt k')]ₚ := by
  cases p with simp [invConst]
  | rel => ext; simp [Term.invConst_subst]
  | eq => simp [Term.invConst_subst]
  | imp p q => simp [invConst_subst (p := p), invConst_subst (p := q)]
  | all p =>
    rw [invConst_subst (k := k + 1) (p := p)]
    congr; funext x
    cases' x using Fin.cases with x
    · simp [Subst.insertAt, Vec.head, Term.invConst, Fin.insertAt]
    · simp [Subst.insertAt, Vec.tail, Function.comp, Fin.embedAt, Term.invConst]
      rcases Fin.embedAt_or_insertAt x with h | ⟨y, h⟩
      · simp [h, Subst.insertAt_app_embedAt]
      · simp [h, Subst.insertAt_app_insertAt, Term.invConst_shift]

theorem Formula.invConst_shift {p : 𝓛.Formula (n + k)} :
  (↑ₚp).invConst (k + 1) c = ↑ₚ(p.invConst k c) := by
  rw [shift, invConst_subst]
  congr; funext x; simp [Function.comp, invConst, Fin.embedAt]
  rcases Fin.embedAt_or_insertAt x with h | ⟨y, h⟩
  · simp [h, Subst.insertAt_app_embedAt]
  · simp [h, Subst.insertAt_app_insertAt, Term.invConst, Fin.insertAt]

theorem Formula.invConst_subst_single {p : 𝓛.Formula (n + k + 1)} {t : 𝓛.Term (n + k)} :
  (p[↦ₛ t]ₚ).invConst k c = (p.invConst (k + 1) c)[↦ₛ (t.invConst k c)]ₚ := by
  rw [invConst_subst (k := k + 1)]
  congr; clear p; funext x
  cases x using Fin.cases with
  | zero => simp [Subst.insertAt, Vec.head]
  | succ x =>
    simp [Subst.insertAt, Vec.tail, Function.comp, Term.invConst]
    rcases Fin.embedAt_or_insertAt x with h | ⟨y, h⟩
    · simp [h, Subst.insertAt_app_embedAt]
    · simp [h, Subst.insertAt_app_insertAt, Term.invConst]

lemma Axiom.inv_const {p : 𝓛.Formula (n + k)} :
  p ∈ 𝓛.Axiom → Γ ⊢ p.invConst k c := by
  intro h
  cases h with simp [Formula.invConst, Formula.invConst_andN, Formula.invConst_shift, Formula.invConst_subst_single]
  | @eq_congr_func m _ v₁ v₂ f =>
    cases m with
    | zero => by_cases h : f = c <;> simp [Term.invConst, h] <;> pintro <;> prefl
    | succ m => simp [Term.invConst]; exact Proof.ax eq_congr_func
  | all h => pintro; exact inv_const (k := k + 1) h
  | _ => apply Proof.ax; constructor

lemma Proof.inv_const {p : 𝓛.Formula (n + k)} (h₁ : ∀ p ∈ Γ, c ∉ p.consts) :
  Γ ⊢ p → (·[Subst.shiftAt k]ₚ) '' Γ ⊢ p.invConst k c := by
  intro h
  induction h with
  | @hyp p h => apply hyp; exists p, h; rw [Formula.invConst_eq_shiftAt (h₁ p h)]
  | ax h => exact Axiom.inv_const h
  | mp _ _ ih₁ ih₂ => simp at ih₁; exact mp ih₁ ih₂

theorem Proof.const_generalization {Γ : 𝓛.FormulaSet n}
  (h₁ : ∀ p ∈ Γ, c ∉ p.consts) (h₂ : c ∉ p.consts) :
  Γ ⊢ p[↦ₛ c]ₚ → Γ ⊢ ∀' p := by
  intro h
  apply inv_const (k := 0) (c := c) h₁ at h
  rw [←Subst.singleAt, Formula.subst_singleAt_invConst (k := 0) h₂] at h
  exact forall_intro h



inductive henkinStep.Func (𝓛 : Language) (n : ℕ) : ℕ → Type u
| inj : 𝓛.Func m → Func 𝓛 n m
| wit : 𝓛.Formula (n + 1) → Func 𝓛 n 0

def henkinStep (𝓛 : Language) (n : ℕ) : Language where
  Func := henkinStep.Func 𝓛 n
  Rel := 𝓛.Rel

namespace henkinStep

variable {𝓛 : Language}

def wit (p : 𝓛.Formula (n + 1)) : (𝓛.henkinStep n).Const := .wit p

@[simps] def hom : 𝓛 →ᴸ 𝓛.henkinStep n where
  onFunc f := .inj f
  onRel r := r

theorem wit_not_in_homTerm : wit p ∉ (hom.onTerm t).consts := by
  induction t with simp [Hom.onTerm, Term.consts]
  | @func m f v ih =>
    cases m <;> simp [Term.consts]
    · simp [wit]
    · exact ih

theorem wit_not_in_homFormula : wit p ∉ (hom.onFormula q).consts := by
  induction q with simp [Hom.onFormula, Formula.consts]
  | rel | eq => simp [wit_not_in_homTerm]
  | imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | all _ ih => simp [ih]

def invTerm : (k : ℕ) → (𝓛.henkinStep n).Term (m + k) → 𝓛.Term (m + k + 1)
| k, #x => #(Fin.insertAt k x)
| k, (.inj f) ⬝ᶠ v => f ⬝ᶠ λ i => invTerm k (v i)
| k, (.wit _) ⬝ᶠ _ => #(Fin.embedAt k)

theorem invTerm_homTerm : invTerm k (hom.onTerm t : (𝓛.henkinStep n).Term _) = t[Subst.shiftAt k]ₜ := by
  induction t with simp [Hom.onTerm, invTerm]
  | var x => simp [Subst.shiftAt_app]
  | func f v ih => ext; simp [ih]

theorem invTerm_subst {σ : (𝓛.henkinStep n).Subst (m + k) (m' + k')} :
  invTerm k' (t[σ]ₜ) = (invTerm k t)[Subst.insertAt k ((invTerm k' ·) ∘ σ) #(Fin.embedAt k')]ₜ := by
  induction t with
  | var x => simp [invTerm, Function.comp, Subst.insertAt_app_insertAt]
  | func f v ih =>
    cases f <;> simp [invTerm]
    · ext; simp [ih]
    · simp [Subst.insertAt_app_embedAt]

theorem invTerm_shift : invTerm (k + 1) (↑ₜt) = ↑ₜ(invTerm k t) := by
  rw [Term.shift, invTerm_subst]
  congr; funext x; simp [Function.comp, invTerm, Fin.embedAt]
  rcases Fin.embedAt_or_insertAt x with h | ⟨y, h⟩
  · simp [h, Subst.insertAt_app_embedAt]
  · simp [h, Subst.insertAt_app_insertAt, invTerm, Fin.insertAt]

def invFormula : (k : ℕ) → (𝓛.henkinStep n).Formula (m + k) → 𝓛.Formula (m + k + 1)
| k, r ⬝ʳ v => r ⬝ʳ λ i => invTerm k (v i)
| k, t₁ ≐ t₂ => invTerm k t₁ ≐ invTerm k t₂
| k, ⊥ => ⊥
| k, p ⇒ q => invFormula k p ⇒ invFormula k q
| k, ∀' p => ∀' (invFormula (k + 1) p)
@[simp] theorem invFormula_false : invFormula k (⊥ : (𝓛.henkinStep n).Formula (m + k)) = ⊥ := by
  rw [←Formula.false_eq]; simp only [invFormula]
@[simp] theorem invFormula_imp {p q : (𝓛.henkinStep n).Formula (m + k)} :
  invFormula k (p ⇒ q) = invFormula k p ⇒ invFormula k q := by
  rw [←Formula.imp_eq]; simp only [invFormula]
@[simp] theorem invFormula_neg : invFormula k (~ p) = ~ invFormula k p := by
  rw [←Formula.neg_eq, invFormula_imp, invFormula_false]; rfl

theorem invFormula_andN {v : Vec ((𝓛.henkinStep n).Formula (m + k)) l} :
  invFormula k (⋀ i, v i) = ⋀ i, invFormula k (v i) := by
  induction l with simp [Formula.andN]
  | zero => simp [Top.top]
  | succ m ih => simp [PropNotation.and, Vec.head, Vec.tail, Function.comp_def, ih]

theorem invFormula_homFormula : invFormula k (hom.onFormula p : (𝓛.henkinStep n).Formula _) = p[Subst.shiftAt k]ₚ := by
  cases p with simp [Hom.onFormula, invFormula]
  | rel | eq => simp [invTerm_homTerm]
  | imp p q => simp [invFormula_homFormula (p := p), invFormula_homFormula (p := q)]
  | all p => simp [invFormula_homFormula (k := k + 1) (p := p), Subst.shiftAt]

theorem invFormula_subst {σ : (𝓛.henkinStep n).Subst (m + k) (m' + k')} :
  invFormula k' (p[σ]ₚ) = (invFormula k p)[Subst.insertAt k ((invTerm k' ·) ∘ σ) #(Fin.embedAt k')]ₚ := by
  cases p with simp [Hom.onFormula, invFormula]
  | rel | eq => simp [invTerm_subst]
  | imp p q => simp [invFormula_subst (p := p), invFormula_subst (p := q)]
  | all p =>
    rw [invFormula_subst (k := k + 1) (p := p)]
    congr; funext x
    cases' x using Fin.cases with x
    · simp [Subst.insertAt, Vec.head, invTerm, Fin.insertAt]
    · simp [Subst.insertAt, Vec.tail, Function.comp, Fin.embedAt, Term.invConst]
      rcases Fin.embedAt_or_insertAt x with h | ⟨y, h⟩
      · simp [h, Subst.insertAt_app_embedAt]
      · simp [h, Subst.insertAt_app_insertAt, invTerm_shift]

theorem invFormula_shift : invFormula (k + 1) (↑ₚp) = ↑ₚ(invFormula k p) := by
  rw [Formula.shift, invFormula_subst]
  congr; funext x; simp [Function.comp, invTerm, Fin.embedAt]
  rcases Fin.embedAt_or_insertAt x with h | ⟨y, h⟩
  · simp [h, Subst.insertAt_app_embedAt]
  · simp [h, Subst.insertAt_app_insertAt, invTerm, Fin.insertAt]

theorem invFormula_subst_single : invFormula k (p[↦ₛ t]ₚ) = (invFormula (k + 1) p)[↦ₛ (invTerm k t)]ₚ := by
  rw [invFormula_subst (k := k + 1)]
  congr; clear p; funext x
  cases x using Fin.cases with
  | zero => simp [Subst.insertAt, Vec.head]
  | succ x =>
    simp [Subst.insertAt, Vec.tail, Function.comp, invTerm]
    rcases Fin.embedAt_or_insertAt x with h | ⟨y, h⟩
    · simp [h, Subst.insertAt_app_embedAt]
    · simp [h, Subst.insertAt_app_insertAt, invTerm]

theorem inv_axiom {p : (𝓛.henkinStep n).Formula (m + k)} : p ∈ (𝓛.henkinStep n).Axiom → Γ ⊢ invFormula k p := by
  intro h
  cases h with simp [invFormula, invFormula_andN, invFormula_shift, invFormula_subst_single]
  | @eq_congr_func m _ v₁ v₂ f =>
    cases m with
    | zero => cases f <;> simp [Vec.eq_nil] <;> pintro <;> prefl
    | succ m => cases f; simp [invTerm]; exact Proof.ax .eq_congr_func
  | all h => pintro; exact inv_axiom (k := k + 1) h
  | _ => apply Proof.ax; constructor

theorem inv_proof : hom.onFormula '' Δ ⊢ p → Δ ⊢ ∀' (invFormula 0 p) := by
  intro h
  induction h with
  | hyp h => rcases h with ⟨p, h, h'⟩; subst h'; rw [invFormula_homFormula]; exact Proof.forall_self.mp (.hyp h)
  | ax h => pintro; exact inv_axiom (k := 0) h
  | mp _ _ ih₁ ih₂ => simp [invFormula_imp (k := 0)] at ih₁; exact (Proof.ax .forall_imp).mp₂ ih₁ ih₂

theorem hom_consistent {Γ : 𝓛.FormulaSet m} (h : Γ ⊢ ∃' ⊤) :
  Consistent Γ → Consistent (hom.onFormula '' Γ : (𝓛.henkinStep n).FormulaSet m) := by
  intro h₁ h₂
  apply inv_proof at h₂
  simp [invFormula_false (k := 0)] at h₂
  exact h₁ ((Proof.iff_mpr.mp Proof.not_forall_iff).mp₂ h h₂)

inductive axioms : (𝓛.henkinStep n).FormulaSet n where
| henkin (p) : axioms (∃' (hom.onFormula p) ⇒ (hom.onFormula p)[↦ₛ (wit p)]ₚ)

end henkinStep

def FormulaSet.henkinStep (Γ : 𝓛.FormulaSet n) : (𝓛.henkinStep n).FormulaSet n :=
  henkinStep.hom.onFormula '' Γ ∪ henkinStep.axioms

theorem FormulaSet.henkinStep.consistent (h : Γ ⊢ ∃' ⊤) :
  Consistent Γ → Consistent Γ.henkinStep := by
  intro h₁ h₂
  apply Proof.compactness at h₂
  rcases h₂ with ⟨Δ, h₂, h₃, h₄⟩
  simp [FormulaSet.henkinStep] at h₂
  apply Set.decompose_subset_union at h₂
  rcases h₂ with ⟨Γ', A, h₂, h₅, h₅'⟩
  subst h₂; simp at h₃; rcases h₃ with ⟨_, h₃⟩
  revert h₄; apply Set.Finite.induction_on' (C := _) h₃
  · intro h₄; simp at h₄
    apply Proof.weaken h₅ at h₄
    exact henkinStep.hom_consistent h h₁ h₄
  · intro a A' h₆ h₆' h₆'' h₄ h₄'
    simp at h₄'; apply Proof.deduction.mpr at h₄'
    rcases h₅' h₆ with ⟨p⟩
    apply h₄
    apply (Proof.not_imp_left.mp h₄').mp
    apply Proof.const_generalization (c := henkinStep.wit p)
    · intro q h; simp at h; rcases h with h | h
      · rcases h₅ h with ⟨q', _, h⟩; subst h; apply henkinStep.wit_not_in_homFormula
      · rcases h₅' (h₆' h) with ⟨q⟩
        simp [Formula.consts, Formula.consts_of_subst]
        constructor
        · apply henkinStep.wit_not_in_homFormula
        · intro x h
          cases x using Fin.cases with simp [Formula.consts, Term.consts]
          | zero => intro h; apply henkinStep.Func.wit.inj at h; subst h; contradiction
    · simp [Formula.consts]; apply henkinStep.wit_not_in_homFormula
    · exact Proof.not_imp_right.mp h₄'

def henkinChain (𝓛 : Language) (n : ℕ) : ℕ → Language
| 0 => 𝓛
| i + 1 => (𝓛.henkinChain n i).henkinStep n

def henkinize (𝓛 : Language) (n : ℕ) : Language := (DirectedSystem.ofChain (𝓛.henkinChain n) (λ _ => henkinStep.hom)).directLimit

namespace FormulaSet

def henkinChain (Γ : 𝓛.FormulaSet n) : (i : ℕ) → (𝓛.henkinChain n i).FormulaSet n
| 0 => Γ
| i + 1 => (Γ.henkinChain i).henkinStep

def henkinize (Γ : 𝓛.FormulaSet n) : (𝓛.henkinize n).FormulaSet n :=
  ⋃i, (DirectedSystem.homLimit _ i).onFormula '' Γ.henkinChain i

variable {Γ : 𝓛.FormulaSet n}

theorem henkinize.supset_henkin : Γ.henkinize ⊆ Δ → Henkin Δ := by
  intro h₁ p h₂
  rcases DirectedSystem.formula_of_homLimit p with ⟨i, q, h₃⟩
  exists (DirectedSystem.homLimit _ (i + 1)).onFunc (henkinStep.wit q)
  revert h₂; apply Proof.mp
  apply Proof.hyp
  apply h₁
  rw [←DirectedSystem.homLimit_comp_hom (h := Nat.le_succ i)] at h₃
  simp [Hom.comp_onFormula, DirectedSystem.ofChain_hom_succ] at h₃
  simp [henkinize]
  exists i + 1, _, .inr (henkinStep.axioms.henkin q)
  simp [h₃, Hom.onFormula, Hom.onTerm, Hom.onFormula_subst_single, Hom.id_onFormula, Vec.eq_nil]
  rfl

variable (h₁ : Γ ⊢ ∃' ⊤)
include h₁

lemma henkinChain.nontrivial : {i : ℕ} → Γ.henkinChain i ⊢ ∃' ⊤
| 0 => h₁
| _ + 1 => Proof.weaken (Set.subset_union_left) (henkinStep.hom.on_proof nontrivial)

variable (h₂ : Consistent Γ)
include h₂

theorem henkinChain.consistent : {i : ℕ} → Consistent (Γ.henkinChain i)
| 0 => h₂
| _ + 1 => henkinStep.consistent (nontrivial h₁) consistent

theorem henkinize.consistent : Consistent Γ.henkinize := by
  intro h
  apply DirectedSystem.proof_of_homLimit at h
  rcases h with ⟨i, Δ, p, h₃, h₄, h₅, h₆⟩
  cases p <;> simp [Hom.onFormula] at h₄
  rcases DirectedSystem.subset_of_monotone_union
    (DirectedSystem.monotone_chain λ _ => Set.subset_union_left) h₃ h₅ with ⟨j, h₇, h₈⟩
  apply henkinChain.consistent h₁ h₂
  apply Proof.weaken h₈
  exact Hom.on_proof h₆
