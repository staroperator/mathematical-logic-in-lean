import Mathlib.Data.Set.Finite
import MathematicalLogic.FirstOrder.Syntax

namespace FirstOrder.Language

variable {𝓛 : Language}

abbrev Context (𝓛 : Language) := Set 𝓛.Formula

def Context.append (Γ : 𝓛.Context) (p) := insert p Γ
infixl:51 ",, " => Context.append

def Context.lift : 𝓛.Context → 𝓛.Context := λ Γ => {↑ₚp | p ∈ Γ}
prefix:max "↑ᶜ" => Context.lift
theorem Context.lift_append : ↑ᶜ(Γ,, p) = ↑ᶜΓ,, ↑ₚp := Set.image_insert_eq

inductive Axioms (𝓛 : Language) : 𝓛.Context where
| a1 {p q : 𝓛.Formula} :
  𝓛.Axioms (p ⇒ (q ⇒ p))
| a2 {p q r : 𝓛.Formula} :
  𝓛.Axioms ((p ⇒ q ⇒ r) ⇒ (p ⇒ q) ⇒ p ⇒ r)
| a3 {p q : 𝓛.Formula} :
  𝓛.Axioms ((~ p ⇒ ~ q) ⇒ q ⇒ p)
| a4 {t : 𝓛.Term} {p : 𝓛.Formula} :
  𝓛.Axioms (∀' p ⇒ p[↦ₛ t]ₚ)
| a5 {p : 𝓛.Formula} :
  𝓛.Axioms (p ⇒ ∀' ↑ₚp)
| a6 {p q : 𝓛.Formula} :
  𝓛.Axioms (∀' (p ⇒ q) ⇒ ∀' p ⇒ ∀' q)
| e1 {t : 𝓛.Term} :
  𝓛.Axioms (t ≐ t)
| e2 {t₁ t₂ : 𝓛.Term} {p : 𝓛.Formula} :
  𝓛.Axioms ((t₁ ≐ t₂) ⇒ p[↦ₛ t₁]ₚ ⇒ p[↦ₛ t₂]ₚ)
| all {p : 𝓛.Formula} :
  𝓛.Axioms p → 𝓛.Axioms (∀' p)

theorem Axioms.closed_under_subst : p ∈ 𝓛.Axioms → p[σ]ₚ ∈ 𝓛.Axioms := by
  intro h
  induction h generalizing σ
    <;> simp [Formula.subst_swap, Formula.shift_subst_lift]
  case all ih => exact all ih
  all_goals constructor

inductive Proof (Γ : 𝓛.Context) : 𝓛.Formula → Prop where
| hyp : p ∈ Γ → Proof Γ p
| ax : p ∈ 𝓛.Axioms → Proof Γ p
| mp : Proof Γ (p ⇒ q) → Proof Γ p → Proof Γ q
infix:50 " ⊢ " => Proof

namespace Proof

variable {Γ Δ : 𝓛.Context} {t t₁ t₂ : 𝓛.Term} {p q r : 𝓛.Formula}

theorem hyp_append : Γ,, p ⊢ p :=
  hyp (Set.mem_insert _ _)

theorem weaken : Γ ⊆ Δ → Γ ⊢ p → Δ ⊢ p := by
  intros h₁ h₂
  induction h₂ with
  | hyp h => exact hyp (h₁ h)
  | ax h => exact ax h
  | mp _ _ ih₁ ih₂ => exact mp ih₁ ih₂

theorem weaken_append : Γ ⊢ p → Γ,, q ⊢ p :=
  weaken (Set.subset_insert _ _)

theorem mp2 : Γ ⊢ p ⇒ q ⇒ r → Γ ⊢ p → Γ ⊢ q → Γ ⊢ r :=
  λ h₁ h₂ h₃ => mp (mp h₁ h₂) h₃

theorem identity : Γ ⊢ p ⇒ p :=
  mp2 (ax .a2) (ax .a1) (ax (.a1 (q := p)))

theorem deduction : Γ ⊢ p ⇒ q ↔ Γ,, p ⊢ q := by
  constructor
  · intro h; exact mp (weaken_append h) hyp_append
  · intro h
    induction h with
    | hyp h =>
      cases h with
      | inl h => subst h; exact identity
      | inr h => exact mp (ax .a1) (hyp h)
    | ax h => exact mp (ax .a1) (ax h)
    | mp _ _ ih₁ ih₂ => exact mp (mp (ax .a2) ih₁) ih₂

theorem cut : Γ ⊢ p → Γ,, p ⊢ q → Γ ⊢ q :=
  λ h₁ h₂ => mp (deduction.mpr h₂) h₁

lemma closed_under_subst : Γ ⊢ p → { q[σ]ₚ | q ∈ Γ } ⊢ p[σ]ₚ := by
  intro h
  induction h with
  | hyp h => apply hyp; exists _, h
  | ax h => exact ax (Axioms.closed_under_subst h)
  | mp _ _ ih₁ ih₂ => exact mp ih₁ ih₂

theorem closed_under_shift : Γ ⊢ p → ↑ᶜΓ ⊢ ↑ₚp := closed_under_subst

macro "pintro" : tactic => `(tactic| apply deduction.mpr)
elab "pintros" n:(ppSpace colGt num)? : tactic => do
  match n with
  | some n =>
    for _ in [:n.getNat] do
      Lean.Elab.Tactic.evalTactic (←`(tactic| pintro))
  | none =>
    Lean.Elab.Tactic.evalTactic (←`(tactic| repeat pintro))

private def hypTerm (n : ℕ) : Lean.MacroM (Lean.TSyntax `term) := do
  let mut t ← `(hyp_append)
  for _ in [:n] do
    t ← `(weaken_append $t)
  return t

macro "passumption" n:(ppSpace colGt num)? : tactic => do
  match n with
  | some n => `(tactic| exact $(← hypTerm n.getNat))
  | none => `(tactic| (apply hyp; repeat first | exact Or.inl rfl | apply Or.inr))

macro "phave" t:(ppSpace colGt term) : tactic =>
  `(tactic| refine cut (p := $t) ?_ ?_)
macro "psuffices" t:(ppSpace colGt term) : tactic =>
  `(tactic| (refine cut (p := $t) ?_ ?_; swap))

/--
  Unify `Γ ⊆ Δ` as `Γ, p₁, ⋯, pₙ = Δ`.
  Return `some n` if succeed, and `none` if fail. -/
private partial def isSubsetOf (Γ Δ : Lean.Expr) : Lean.MetaM (Option ℕ) := do
  let s ← Lean.MonadBacktrack.saveState
  if ← Lean.Meta.isDefEq Γ Δ then
    return some 0
  Lean.MonadBacktrack.restoreState s
  if let some (_, Δ', _) := Δ.app3? ``Context.append then
    if let some n := ← isSubsetOf Γ Δ' then
      return some (n + 1)
  return none

/--
  Given a proof term of `Γ ⊢ p₁ ⇒ ⋯ ⇒ pₙ`, apply it on the goal `Γ' ⊢ pₙ` through MP.
  `Γ` should be a subset of `Γ'`.
  
  Control the application depth `n` through `with` clause. -/
elab "papply" t:(ppSpace colGt term) d:((" with " num)?) : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let appTerm ← Lean.Elab.Term.elabTerm t none
    let appType ← Lean.instantiateMVars (← Lean.Meta.inferType appTerm)
    let (forallMVars, _, type) ← Lean.Meta.forallMetaTelescopeReducing appType
    let (Lean.mkApp3 (.const ``Proof []) 𝓛 Γ p) := type
      | throwError m!"{type} is not a proof"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← goal.getType'
    let some (𝓛', Δ, _) := goalType.app3? ``Proof
      | throwError m!"{goalType} is not a proof"
    let true := ← Lean.Meta.isDefEq 𝓛 𝓛'
      | throwError m!"failed to unify {𝓛} and {𝓛'}"
    let some weakenDepth := ← isSubsetOf Γ Δ
      | throwError m!"failed to unify {Γ} as a subset of {Δ}"
    let weakenTy ← do
      let weakenTy := Lean.mkApp3
        (.const ``Set.Subset [0]) (.app (.const ``Formula []) 𝓛) Γ Δ
      Lean.Meta.checkTypeIsProp weakenTy
      pure weakenTy
    let weakenTerm ← do
      let mut weakenTerm ← `(Set.Subset.refl _)
      for _ in [:weakenDepth] do
        weakenTerm := ← `(Set.Subset.trans $weakenTerm (Set.subset_insert _ _))
      Lean.Elab.Term.elabTerm weakenTerm (some weakenTy)
    let mut proofTerm := Lean.mkApp6
      (.const ``weaken []) 𝓛 Γ Δ p weakenTerm
      (Lean.mkAppN appTerm forallMVars)
    let mut newMVarIds := []
    let mut goalFormula := p
    let maxDepth := d.raw.getArgs[1]?.map (·.toNat)
    repeat do
      let proofType ← Lean.Meta.inferType proofTerm
      if ← Lean.Meta.isDefEq goalType proofType then
        goal.assign proofTerm
        break
      if let some d := maxDepth then
        if newMVarIds.length >= d then
          throwError "failed to apply {appType} at {goalType} within depth {d}"
      else if let some (_, p, q) := (← Lean.Meta.whnf goalFormula).app3? ``Formula.imp then
        let mvarId ← Lean.mkFreshMVarId
        newMVarIds := newMVarIds ++ [mvarId]
        let mvar ← Lean.Meta.mkFreshExprMVarWithId mvarId (some (
          Lean.mkApp3 (.const ``Proof []) 𝓛 Δ p))
        let newProofTerm := Lean.mkApp6
          (.const ``mp []) 𝓛 Δ p q proofTerm mvar
        proofTerm := newProofTerm
        goalFormula := q
      else
        throwError "failed to apply {appType} at {goalType}"
    for mvar in forallMVars do
      if let (.mvar mvarid) := mvar then
        if !(← mvarid.isAssigned) then
          newMVarIds := newMVarIds ++ [mvarid]
    Lean.Elab.Tactic.replaceMainGoal newMVarIds

/-- Apply an assumption through MP. -/
macro "papplya" n:(ppSpace colGt num) : tactic => do
  `(tactic| papply $(← hypTerm n.getNat))

/-- Close the goal with given proof term. -/
macro "pexact" t:(ppSpace colGt term) : tactic =>
  `(tactic| papply $t with 0)

theorem composition : Γ ⊢ (p ⇒ q) ⇒ (q ⇒ r) ⇒ p ⇒ r := by
  pintros
  papplya 1
  papplya 2
  passumption

theorem contraposition : Γ ⊢ (p ⇒ q) ⇒ ~ q ⇒ ~ p := composition

theorem contraposition2 : Γ ⊢ (p ⇒ ~ q) ⇒ q ⇒ ~ p := by
  pintros
  papplya 2 <;> passumption

theorem true_intro : Γ ⊢ ⊤ := identity

theorem false_elim : Γ ⊢ ⊥ ⇒ p := by
  papply ax .a3
  pintro
  exact true_intro

theorem contradiction : Γ ⊢ ~ p ⇒ p ⇒ q := by
  pintros
  papply false_elim
  papplya 1
  passumption

theorem double_neg1 : Γ ⊢ p ⇒ ~ ~ p := by
  pintros
  papplya 0
  passumption

theorem double_neg2 : Γ ⊢ ~ ~ p ⇒ p := by
  pintro
  papply ax .a3
  · exact double_neg1
  · passumption

theorem contraposition3 : Γ ⊢ (~ p ⇒ q) ⇒ ~ q ⇒ p := by
  papply composition
  · exact contraposition
  · papply ax .a2
    pintro
    exact double_neg2

theorem not_imp_left : Γ ⊢ ~ (p ⇒ q) ⇒ p := by
  pintro
  papply double_neg2
  papply contraposition
  · exact contradiction (q := q)
  · passumption

theorem not_imp_right : Γ ⊢ ~ (p ⇒ q) ⇒ ~ q := by
  papply contraposition
  exact ax .a1

theorem and_intro : Γ ⊢ p ⇒ q ⇒ p ⩑ q := by
  pintros
  papplya 0 <;> passumption

theorem and_left : Γ ⊢ p ⩑ q ⇒ p := by
  pintro
  papply double_neg2
  pintro
  papplya 1
  pintros
  papply false_elim
  papplya 2
  passumption

theorem and_right : Γ ⊢ p ⩑ q ⇒ q := by
  pintro
  papply double_neg2
  pintro
  papplya 1
  pintro
  passumption

theorem or_inl : Γ ⊢ p ⇒ p ⩒ q := by
  pintros
  papply contradiction <;> passumption

theorem or_inr : Γ ⊢ q ⇒ p ⩒ q := ax .a1

theorem or_elim : Γ ⊢ p ⩒ q ⇒ (p ⇒ r) ⇒ (q ⇒ r) ⇒ r := by
  pintros
  papply double_neg2
  pintro
  papplya 0
  papplya 2
  psuffices ~ p
  · papply contradiction
    · passumption 1
    · papplya 2
      papplya 4
      passumption
  · pintro
    papplya 1
    papplya 3
    passumption

theorem excluded_middle : Γ ⊢ ~ p ⩒ p := double_neg2

theorem andN_intro {v : Vec 𝓛.Formula n} :
  (∀ i, Γ ⊢ v i) → Γ ⊢ ⋀i, v i := by
  intro h
  induction n with
  | zero => exact true_intro
  | succ n ih =>
    papply and_intro
    · apply h
    · apply ih; intro i; apply h

theorem andN_elim {v : Vec 𝓛.Formula n} {i : Fin n} :
  (Γ ⊢ ⋀i, v i) → Γ ⊢ v i := by
  intro h
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact mp and_left h
    | succ i => apply ih (mp and_right h)

theorem iff_intro : Γ ⊢ (p ⇒ q) ⇒ (q ⇒ p) ⇒ (p ⇔ q) := and_intro
theorem iff_mp : Γ ⊢ (p ⇔ q) ⇒ (p ⇒ q) := and_left
theorem iff_mpr : Γ ⊢ (p ⇔ q) ⇒ (q ⇒ p) := and_right
theorem iff_iff : Γ ⊢ p ⇔ q → (Γ ⊢ p ↔ Γ ⊢ q) := λ h => ⟨iff_mp.mp2 h, iff_mpr.mp2 h⟩

theorem iff_refl : Γ ⊢ p ⇔ p := mp2 iff_intro identity identity

theorem iff_symm : Γ ⊢ (p ⇔ q) ⇒ (q ⇔ p) := by
  pintro
  papply iff_intro
  · papply iff_mpr; passumption
  · papply iff_mp; passumption

theorem iff_trans : Γ ⊢ (p ⇔ q) ⇒ (q ⇔ r) ⇒ (p ⇔ r) := by
  pintros 2
  papply iff_intro
  · papply composition <;> papply iff_mp <;> passumption
  · papply composition <;> papply iff_mpr <;> passumption

theorem iff_congr_imp : Γ ⊢ (p₁ ⇔ p₂) ⇒ (q₁ ⇔ q₂) ⇒ ((p₁ ⇒ q₁) ⇔ (p₂ ⇒ q₂)) := by
  pintros 2
  papply iff_intro <;> pintros
  · papply iff_mp; passumption
    papplya 1
    papply iff_mpr; passumption
    passumption
  · papply iff_mpr; passumption
    papplya 1
    papply iff_mp; passumption
    passumption

theorem generalization : ↑ᶜΓ ⊢ p → Γ ⊢ ∀' p := by
  intro h
  induction h with
  | hyp h =>
    rcases h with ⟨p, ⟨h₁, h₂⟩⟩
    subst h₂
    exact mp (ax .a5) (hyp h₁)
  | ax h => exact ax (.all h)
  | mp _ _ ih₁ ih₂ => exact mp2 (ax .a6) ih₁ ih₂

theorem generalization_iff : ↑ᶜΓ ⊢ p ↔ Γ ⊢ ∀' p := by
  constructor
  · exact generalization
  · intro h
    apply closed_under_shift at h
    simp [Formula.shift] at h
    apply mp (ax $ .a4 (t := #0)) at h
    have : p[⇑ₛSubst.shift]ₚ[↦ₛ #0]ₚ = p := by
      rw [←Formula.subst_comp]
      conv => rhs; rw [←Formula.subst_id (p := p)]
      congr; funext x; cases x <;> simp
    rw [this] at h
    exact h

theorem iff_congr_forall : Γ ⊢ ∀' (p ⇔ q) ⇒ ∀' p ⇔ ∀' q := by
  pintro
  papply iff_intro <;> papply ax .a6 <;> rw [←deduction] <;> papply ax .a6
    <;> apply generalization
  · exact iff_mp
  · exact iff_mpr

theorem not_forall : Γ ⊢ ~ ∀' p ⇒ ∃' (~ p) := by
  papply contraposition
  papply ax .a6
  apply generalization
  exact double_neg2

theorem not_exists : Γ ⊢ ~ ∃' p ⇒ ∀' (~ p) := double_neg2

theorem forall_elim : Γ ⊢ ∀' p ⇒ p[↦ₛ t]ₚ := ax .a4

theorem exists_intro : Γ ⊢ p[↦ₛ t]ₚ ⇒ ∃' p := by
  pintros
  suffices _ ⊢ (~ p)[↦ₛ t]ₚ by
    papply this
    passumption
  papply ax .a4
  passumption

theorem exists_elim : Γ ⊢ ∃' p ⇒ (∀' (p ⇒ ↑ₚq)) ⇒ q := by
  pintros
  papply double_neg2
  pintros
  papplya 2
  suffices _ ⊢ ∀' (↑ₚ(~ q) ⇒ ~ p) by
    papply ax .a6
    · exact this
    · papply ax .a5
      passumption
  papply ax .a6
  · apply generalization
    exact contraposition
  · passumption

theorem exists_self : Γ ⊢ ∃' ↑ₚp ⇒ p := by
  papply contraposition3
  apply ax .a5

theorem foralls_elim {p : 𝓛.BFormula m} :
  Γ ⊢ (∀* p).val ⇒ p.val[σ]ₚ := by
  induction' m with m ih generalizing σ
  · rw [Sentence.val_subst_eq]; exact identity
  · let σ' := λ x => σ (x + 1)
    papply composition
    · exact ih (σ := σ')
    · have h : ⇑ₛσ' ∘ₛ ↦ₛ (σ 0) = σ := by
        funext x; cases x <;> simp [Term.shift_subst_single]
      conv in _[σ]ₚ => rw [←h, Formula.subst_comp]
      apply Proof.forall_elim

theorem foralls_elim_self {p : 𝓛.BFormula m} :
  Γ ⊢ (∀* p).val ⇒ p.val := by
  rw [←Formula.subst_id (p := p.val)]
  exact foralls_elim

theorem refl : Γ ⊢ t ≐ t := ax .e1
macro "prefl" : tactic => `(tactic| pexact refl)

theorem subst : Γ ⊢ t₁ ≐ t₂ ⇒ p[↦ₛ t₁]ₚ ⇒ p[↦ₛ t₂]ₚ := ax .e2

theorem symm : Γ ⊢ t₁ ≐ t₂ ⇒ t₂ ≐ t₁ := by
  have h := @subst _ Γ t₁ t₂ (#0 ≐ ↑ₜt₁)
  simp [Term.shift_subst_single] at h
  pintro
  papply h
  · passumption
  · prefl
macro "psymm" : tactic => `(tactic| papply symm)

theorem trans : Γ ⊢ t₁ ≐ t₂ ⇒ t₂ ≐ t₃ ⇒ t₁ ≐ t₃ := by
  have h := @subst _ Γ t₂ t₁ (#0 ≐ ↑ₜt₃)
  simp [Term.shift_subst_single] at h
  pintros
  papply h
  · psymm; passumption
  · passumption
macro "ptrans" t:(ppSpace colGt term)? : tactic =>
  match t with
  | some t => `(tactic| papply trans (t₂ := $t))
  | none => `(tactic| papply trans)

theorem subst_iff : Γ ⊢ t₁ ≐ t₂ ⇒ p[↦ₛ t₁]ₚ ⇔ p[↦ₛ t₂]ₚ := by
  pintro
  papply iff_intro <;> papply subst
  · passumption
  · psymm; passumption

theorem subst_term : Γ ⊢ t₁ ≐ t₂ ⇒ t[↦ₛ t₁]ₜ ≐ t[↦ₛ t₂]ₜ := by
  pintro
  have h := @subst _ Γ t₁ t₂ (↑ₜ(t[↦ₛ t₁]ₜ) ≐ t)
  simp [Term.shift_subst_single] at h
  papply h
  · passumption
  · prefl

theorem congr_func {v₁ v₂ : Vec 𝓛.Term n} :
  Γ ⊢ (⋀i, v₁ i ≐ v₂ i) ⇒ f ⬝ₜ v₁ ≐ f ⬝ₜ v₂ := by
  pintro
  suffices ∀ k ≤ n, _ ⊢ f ⬝ₜ v₁ ≐ f ⬝ₜ (λ i => if i < k then v₂ i else v₁ i) by
    replace this := this n (by rfl)
    simp at this
    exact this
  intros k h₁
  induction k with
  | zero => simp; prefl
  | succ k ih =>
    ptrans
    · exact ih (Nat.le_of_succ_le h₁)
    · let k' : Fin n := ⟨k, h₁⟩
      let t := f ⬝ₜ (λ i => if i < k then ↑ₜ(v₂ i) else if i = k then #0 else ↑ₜ(v₁ i))
      have h₂ : t[↦ₛ (v₁ k')]ₜ = f ⬝ₜ (λ i => if i < k then v₂ i else v₁ i) := by
        simp [t]; ext i
        rcases Nat.lt_trichotomy i k with (h | h | h)
        · simp [h, Term.shift_subst_single]
        · simp [h]; congr; apply Fin.eq_of_val_eq; simp [k', h]
        · simp [Nat.not_lt_of_gt h, Nat.ne_of_gt h, Term.shift_subst_single]
      have h₃ : t[↦ₛ (v₂ k')]ₜ = f ⬝ₜ (λ i => if i < k.succ then v₂ i else v₁ i) := by
        simp [t]; ext i
        rcases Nat.lt_trichotomy i k with (h | h | h)
        · simp [h, Nat.lt_succ_of_lt h, Term.shift_subst_single]
        · simp [h]; congr; apply Fin.eq_of_val_eq; simp [k', h]
        · simp [Nat.not_lt_of_gt h, Nat.lt_succ, Nat.not_le_of_gt h,
            Nat.ne_of_gt h, Term.shift_subst_single]
      rw [←h₂, ←h₃]
      papply subst_term
      apply andN_elim (v := λ i => v₁ i ≐ v₂ i)
      passumption

theorem subst_term' :
  (∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) → Γ ⊢ t[σ₁]ₜ ≐ t[σ₂]ₜ := by
  intro h
  induction t with simp
  | var => apply h
  | func f v ih => papply congr_func; apply andN_intro; exact ih

theorem congr_rel_iff {r} {v₁ v₂ : Vec 𝓛.Term n} :
  Γ ⊢ (⋀i, v₁ i ≐ v₂ i) ⇒ r ⬝ᵣ v₁ ⇔ r ⬝ᵣ v₂ := by
  pintro
  suffices ∀ k ≤ n, _ ⊢ r ⬝ᵣ v₁ ⇔ r ⬝ᵣ (λ i => if i < k then v₂ i else v₁ i) by
    replace this := this n (by rfl)
    simp at this
    exact this
  intros k h₁
  induction k with
  | zero => simp; exact iff_refl
  | succ k ih =>
    papply iff_trans
    · exact ih (Nat.le_of_succ_le h₁)
    · let k' : Fin n := ⟨k, h₁⟩
      let p := r ⬝ᵣ (λ i => if i < k then ↑ₜ(v₂ i) else if i = k then #0 else ↑ₜ(v₁ i))
      have h₂ : p[↦ₛ (v₁ k')]ₚ = r ⬝ᵣ (λ i => if i < k then v₂ i else v₁ i) := by
        simp [p]; ext i
        rcases Nat.lt_trichotomy i k with (h | h | h)
        · simp [h, Term.shift_subst_single]
        · simp [h]; congr; apply Fin.eq_of_val_eq; simp [k', h]
        · simp [Nat.not_lt_of_gt h, Nat.ne_of_gt h, Term.shift_subst_single]
      have h₃ : p[↦ₛ (v₂ k')]ₚ = r ⬝ᵣ (λ i => if i < k.succ then v₂ i else v₁ i) := by
        simp [p]; ext i
        rcases Nat.lt_trichotomy i k with (h | h | h)
        · simp [h, Nat.lt_succ_of_lt h, Term.shift_subst_single]
        · simp [h]; congr; apply Fin.eq_of_val_eq; simp [k', h]
        · simp [Nat.not_lt_of_gt h, Nat.lt_succ, Nat.not_le_of_gt h,
            Nat.ne_of_gt h, Term.shift_subst_single]
      rw [←h₂, ←h₃]
      papply subst_iff
      apply andN_elim (v := λ i => v₁ i ≐ v₂ i)
      passumption

theorem congr_rel {r} {v₁ v₂ : Vec 𝓛.Term n} :
  Γ ⊢ (⋀i, v₁ i ≐ v₂ i) ⇒ r ⬝ᵣ v₁ ⇒ r ⬝ᵣ v₂ := by
  pintro
  papply iff_mp
  papply congr_rel_iff
  passumption

theorem congr_eq : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ ≐ t₂ ⇒ t₁' ≐ t₂' := by
  pintros
  ptrans
  · psymm; passumption
  · ptrans <;> passumption

theorem congr_eq_iff : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ ≐ t₂ ⇔ t₁' ≐ t₂' := by
  pintros 2
  papply iff_intro
  · papply congr_eq <;> passumption
  · papply congr_eq <;> psymm <;> passumption

theorem subst_iff' : (∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) → Γ ⊢ p[σ₁]ₚ ⇔ p[σ₂]ₚ := by
  intro h
  induction p generalizing Γ σ₁ σ₂ with simp
  | rel r v =>
    papply congr_rel_iff; apply andN_intro; intro; apply subst_term'; exact h
  | eq t₁ t₂ =>
    papply congr_eq_iff <;> apply subst_term' <;> exact h
  | false =>
    exact iff_refl
  | imp p q ih₁ ih₂ =>
    papply iff_congr_imp <;> apply_assumption <;> exact h
  | all p ih =>
    papply iff_congr_forall; apply generalization; apply ih; intro i
    cases i with simp
    | zero => prefl
    | succ i => apply closed_under_shift (p := σ₁ i ≐ σ₂ i); apply h

theorem subst' : (∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) → Γ ⊢ p[σ₁]ₚ ⇒ p[σ₂]ₚ := by
  intro h
  papply iff_mp
  exact subst_iff' h

namespace Rewrite

mutual
inductive Term (Γ : 𝓛.Context) : 𝓛.Term → 𝓛.Term → Prop
| matched {t₁ t₂} : Γ ⊢ t₁ ≐ t₂ → Term Γ t₁ t₂
| func : Terms Γ v₁ v₂ → Term Γ (f ⬝ₜ v₁) (f ⬝ₜ v₂)
| refl {t} : Term Γ t t
inductive Terms (Γ : 𝓛.Context) : Vec 𝓛.Term n → Vec 𝓛.Term n → Prop
| cons {t₁ t₂} : Term Γ t₁ t₂ → Terms Γ v₁ v₂ → Terms Γ (t₁ ∷ᵥ v₁) (t₂ ∷ᵥ v₂)
| refl : Terms Γ v v
end

theorem Terms.term :
  ∀ {n} {v₁ v₂ : Vec 𝓛.Term n}, Terms Γ v₁ v₂ → ∀ i, Term Γ (v₁ i) (v₂ i)
| _, _, _, cons h₁ h₂, i => i.cases h₁ (λ _ => h₂.term _)
| _, _, _, refl, _ => Term.refl

theorem Term.sound : ∀ {t₁ t₂}, Term Γ t₁ t₂ → Γ ⊢ t₁ ≐ t₂
| _, _, matched h => h
| _, _, func h => by
  papply congr_func; apply andN_intro; intro i; exact (h.term i).sound
| _, _, refl => Proof.refl

inductive Formula (Γ : 𝓛.Context) : 𝓛.Formula → 𝓛.Formula → Prop
| rel {r v₁ v₂} : Terms Γ v₁ v₂ → Formula Γ (r ⬝ᵣ v₁) (r ⬝ᵣ v₂)
| eq {t₁ t₁' t₂ t₂'} : Term Γ t₁ t₁' → Term Γ t₂ t₂' → Formula Γ (t₁ ≐ t₂) (t₁' ≐ t₂')
| imp {p₁ q₁ p₂ q₂} : Formula Γ p₁ q₁ → Formula Γ p₂ q₂ → Formula Γ (p₁ ⇒ p₂) (q₁ ⇒ q₂)
| refl {p} : Formula Γ p p

theorem Formula.sound : Formula Γ p q → Γ ⊢ p ⇔ q := by
  intro h
  induction h with
  | rel h => papply congr_rel_iff; apply andN_intro; intro i; exact (h.term i).sound
  | eq => papply congr_eq_iff <;> apply Term.sound <;> assumption
  | imp => papply iff_congr_imp <;> assumption
  | refl => exact iff_refl

macro "prewrite" t:term : tactic =>
  `(tactic| (
    apply mp2 iff_mpr
    · apply Formula.sound
      repeat' first
      | apply Formula.rel | apply Formula.eq | apply Formula.imp | exact Formula.refl
      | apply Terms.cons | exact Terms.refl
      | exact Term.matched (by pexact $t) | apply Term.func | exact Term.refl
    try simp))

syntax rwRule := ("← "?) term

/--
  Rewrite goal using given terms.
  If a number instead of term is given, it will use assumption in rewrite.
  
  Use `←` to change the direction. -/
elab "prw" "[" rules:withoutPosition(rwRule,*,?) "]" : tactic => do
  for rule in rules.raw.getSepArgs do
    let t ←
      match rule with
      | `(rwRule | $n:num) => Lean.Elab.liftMacroM (hypTerm n.getNat)
      | `(rwRule | $t:term) => pure t
      | `(rwRule | ← $n:num) => `(mp symm $(← Lean.Elab.liftMacroM (hypTerm n.getNat)))
      | `(rwRule | ← $t:term) => `(mp symm $t)
      | _ => throwError "this shouldn't happen"
    Lean.Elab.Tactic.evalTactic (←`(tactic| prewrite $t))

end Rewrite

theorem compactness : Γ ⊢ p → ∃ Δ, Δ ⊆ Γ ∧ Δ.Finite ∧ Δ ⊢ p := by
  intro h
  induction h with
  | @hyp p h =>
    exists {p}; simp [h]
    passumption; rfl
  | ax h =>
    exists ∅; simp
    exact ax h
  | mp _ _ ih₁ ih₂ =>
    rcases ih₁ with ⟨Δ₁, h₁, h₂, h₃⟩
    rcases ih₂ with ⟨Δ₂, h₄, h₅, h₆⟩
    exists Δ₁ ∪ Δ₂; simp [h₁, h₄, h₂, h₅]
    apply Proof.mp
    · apply weaken _ h₃; simp
    · apply weaken _ h₆; simp

end Proof

notation Γ:50 "⊬" p:50 => ¬ Γ ⊢ p

namespace Context

def Consistent (Γ : 𝓛.Context) := Γ ⊬ ⊥

theorem Consistent.weaken : Γ ⊆ Δ → Consistent Δ → Consistent Γ := by
  intros h₁ h₂ h
  apply h₂
  exact Proof.weaken h₁ h

theorem Consistent.append : Consistent (Γ,, p) ↔ Γ ⊬ ~ p := by
  constructor
  · intro h₁ h₂
    apply h₁
    rw [←Proof.deduction]
    exact h₂
  · intro h₁ h₂
    apply h₁
    pintro
    exact h₂

end Language.Context
