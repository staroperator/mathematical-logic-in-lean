import Mathlib.Data.Set.Finite
import MathematicalLogic.FirstOrder.Syntax

namespace FirstOrder.Language

inductive Axioms (𝓛 : Language) : 𝓛.FormulaSet n where
| imp_self {p q} : 𝓛.Axioms (p ⇒ q ⇒ p)
| imp_distrib {p q r} : 𝓛.Axioms ((p ⇒ q ⇒ r) ⇒ (p ⇒ q) ⇒ p ⇒ r)
| transpose {p q} : 𝓛.Axioms ((~ p ⇒ ~ q) ⇒ q ⇒ p)
| forall_elim {t p} : 𝓛.Axioms (∀' p ⇒ p[↦ₛ t]ₚ)
| forall_self {p} : 𝓛.Axioms (p ⇒ ∀' ↑ₚp)
| forall_imp {p q} : 𝓛.Axioms (∀' (p ⇒ q) ⇒ ∀' p ⇒ ∀' q)
| eq_refl {t} : 𝓛.Axioms (t ≐ t)
| eq_subst {t₁ t₂ p} : 𝓛.Axioms (t₁ ≐ t₂ ⇒ p[↦ₛ t₁]ₚ ⇒ p[↦ₛ t₂]ₚ)
| all {p} : 𝓛.Axioms p → 𝓛.Axioms (∀' p)

variable {𝓛 : Language}

theorem Axioms.subst {σ : 𝓛.Subst n m} : p ∈ 𝓛.Axioms → p[σ]ₚ ∈ 𝓛.Axioms := by
  intro h
  induction h generalizing m <;> simp [Term.shift_subst_lift, Formula.shift_subst_lift, Formula.subst_swap_single]
  case all ih => exact all ih
  all_goals constructor

inductive Proof (Γ : 𝓛.FormulaSet n) : 𝓛.Formula n → Prop where
| hyp : p ∈ Γ → Proof Γ p
| ax : p ∈ 𝓛.Axioms → Proof Γ p
| mp : Proof Γ (p ⇒ q) → Proof Γ p → Proof Γ q
infix:50 " ⊢ " => Proof

namespace Proof

variable {n} {Γ : 𝓛.FormulaSet n}

theorem hyp_append : Γ,' p ⊢ p := hyp (Set.mem_insert _ _)

theorem weaken : Γ ⊆ Δ → Γ ⊢ p → Δ ⊢ p := by
  intros h₁ h₂
  induction h₂ with
  | hyp h => exact hyp (h₁ h)
  | ax h => exact ax h
  | mp _ _ ih₁ ih₂ => exact mp ih₁ ih₂

theorem weaken_append : Γ ⊢ p → Γ,' q ⊢ p := weaken (Set.subset_insert _ _)

theorem mp₂ (h₁ : Γ ⊢ p ⇒ q ⇒ r) (h₂ : Γ ⊢ p) (h₃ : Γ ⊢ q) : Γ ⊢ r := mp (mp h₁ h₂) h₃

theorem identity : Γ ⊢ p ⇒ p :=
  mp₂ (ax .imp_distrib) (ax .imp_self) (ax (.imp_self (q := p)))

theorem deduction : Γ ⊢ p ⇒ q ↔ Γ,' p ⊢ q := by
  constructor
  · intro h; exact mp (weaken_append h) hyp_append
  · intro h
    induction h with
    | hyp h =>
      cases h with
      | inl h => subst h; exact identity
      | inr h => exact mp (ax .imp_self) (hyp h)
    | ax h => exact mp (ax .imp_self) (ax h)
    | mp _ _ ih₁ ih₂ => exact mp (mp (ax .imp_distrib) ih₁) ih₂

theorem cut (h₁ : Γ ⊢ p) (h₂ : Γ,' p ⊢ q) : Γ ⊢ q := mp (deduction.mpr h₂) h₁

theorem subst : Γ ⊢ p → (·[σ]ₚ) '' Γ ⊢ p[σ]ₚ := by
  intro h
  induction h with
  | hyp h => apply hyp; exists _, h
  | ax h => exact ax (.subst h)
  | mp _ _ ih₁ ih₂ => exact mp ih₁ ih₂

theorem shift : Γ ⊢ p → ↑ᴳΓ ⊢ ↑ₚp := subst

theorem forall_imp : Γ ⊢ ∀' (p ⇒ q) ⇒ ∀' p ⇒ ∀' q := ax .forall_imp
theorem forall_elim : Γ ⊢ ∀' p ⇒ p[↦ₛ t]ₚ := ax .forall_elim
theorem forall_self : Γ ⊢ p ⇒ ∀' ↑ₚp := ax .forall_self

theorem generalization : ↑ᴳΓ ⊢ p ↔ Γ ⊢ ∀' p := by
  constructor
  · intro h
    induction h with
    | hyp h =>
      rcases h with ⟨p, ⟨h₁, h₂⟩⟩
      subst h₂
      exact forall_self.mp (hyp h₁)
    | ax h => exact ax (.all h)
    | mp _ _ ih₁ ih₂ => exact forall_imp.mp₂ ih₁ ih₂
  · intro h
    apply shift at h
    simp [Formula.shift] at h
    apply forall_elim.mp at h
    have : p[⇑ₛSubst.shift]ₚ[↦ₛ #0]ₚ = p := by
      rw [←Formula.subst_comp]
      conv => rhs; rw [←Formula.subst_id (p := p)]
      congr; funext x; cases x using Fin.cases <;> simp
    rw [this] at h
    exact h

theorem forall_intro : ↑ᴳΓ ⊢ p → Γ ⊢ ∀' p := generalization.mp

/--
  Introduce a new hypothesis through deduction theorem, or introduce a new variable
  through generalization theorem. -/
macro "pintro" : tactic => `(tactic| first | apply deduction.mpr | apply forall_intro)

/-- Revert a hypothesis through deduction theorem. -/
macro "prevert" : tactic => `(tactic| apply deduction.mp)

/-- Repeatly introduce new hypotheses and variables. -/
macro "pintros" n:(ppSpace colGt num)? : tactic =>
  match n with
  | some n => `(tactic| iterate $n pintro)
  | none => `(tactic| repeat pintro)

private def hypTerm (n : ℕ) : Lean.MacroM (Lean.TSyntax `term) := do
  let mut t ← `(hyp_append)
  for _ in [:n] do
    t ← `(weaken_append $t)
  return t

/--
  Close the proof goal using assumption.
  If a number `n` is given, the `n`-th assumption (from right to left) will be used.
  Otherwise, this tactic will try to search for such an assumption. -/
macro "passumption" n:(ppSpace colGt num)? : tactic => do
  match n with
  | some n => `(tactic| exact $(← hypTerm n.getNat))
  | none => `(tactic| (apply hyp; repeat first | exact Or.inl rfl | apply Or.inr))

macro "phave" t:(ppSpace colGt term) : tactic =>
  `(tactic| refine cut (p := $t) ?_ ?_)
macro "psuffices" t:(ppSpace colGt term) : tactic =>
  `(tactic| (refine cut (p := $t) ?_ ?_; swap))

/--
  Unify `Γ ⊆ Δ` as `Γ, p₁, ⋯, pₙ = Δ`. Return `some n` if succeed, and `none` if fail. -/
private partial def isSubsetOf (Γ Δ : Lean.Expr) : Lean.MetaM (Option ℕ) := do
  let s ← Lean.MonadBacktrack.saveState
  if ← Lean.Meta.isDefEq Γ Δ then
    return some 0
  Lean.MonadBacktrack.restoreState s
  if let some (_, _, Δ', _) := Δ.app4? ``FormulaSet.append then
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
    let (Lean.mkApp4 (.const ``Proof []) 𝓛 n Γ p) := type
      | throwError m!"{type} is not a proof"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← goal.getType'
    let some (𝓛', m, Δ, _) := goalType.app4? ``Proof
      | throwError m!"{goalType} is not a proof"
    let true := ← Lean.Meta.isDefEq n m
      | throwError m!"failed to unify {n} and {m}"
    let true := ← Lean.Meta.isDefEq 𝓛 𝓛'
      | throwError m!"failed to unify {𝓛} and {𝓛'}"
    let some weakenDepth := ← isSubsetOf Γ Δ
      | throwError m!"failed to unify {Γ} as a subset of {Δ}"
    let weakenTy ← do
      let weakenTy := Lean.mkApp3
        (.const ``Set.Subset [0]) (Lean.mkApp2 (.const ``Formula []) 𝓛 n) Γ Δ
      pure weakenTy
    let weakenTerm ← do
      let mut weakenTerm ← `(Set.Subset.refl _)
      for _ in [:weakenDepth] do
        weakenTerm := ← `(Set.Subset.trans $weakenTerm (Set.subset_insert _ _))
      Lean.Elab.Term.elabTerm weakenTerm (some weakenTy)
    let mut proofTerm := Lean.mkApp7
      (.const ``weaken []) 𝓛 n Γ Δ p weakenTerm
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
      else if let some (_, _, p, q) := (← Lean.Meta.whnf goalFormula).app4? ``Formula.imp then
        let mvarId ← Lean.mkFreshMVarId
        newMVarIds := newMVarIds ++ [mvarId]
        let mvar ← Lean.Meta.mkFreshExprMVarWithId mvarId (some (
          Lean.mkApp4 (.const ``Proof []) 𝓛 n Δ p))
        let newProofTerm := Lean.mkApp7
          (.const ``mp []) 𝓛 n Δ p q proofTerm mvar
        proofTerm := newProofTerm
        goalFormula := q
      else
        throwError "failed to apply {appType} at {goalType}"
    for mvar in forallMVars do
      if let (.mvar mvarid) := mvar then
        if !(← mvarid.isAssigned) then
          newMVarIds := newMVarIds ++ [mvarid]
    Lean.Elab.Tactic.replaceMainGoal newMVarIds

/-- Apply the `n`-th assumption through MP. -/
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

theorem transpose : Γ ⊢ (~ p ⇒ ~ q) ⇒ q ⇒ p := ax .transpose

theorem transpose₂ : Γ ⊢ (p ⇒ q) ⇒ ~ q ⇒ ~ p := composition

theorem transpose₃ : Γ ⊢ (p ⇒ ~ q) ⇒ q ⇒ ~ p := by
  pintros
  papplya 2 <;> passumption

theorem true_intro : Γ ⊢ ⊤ := identity

theorem false_elim : Γ ⊢ ⊥ ⇒ p := by
  papply transpose
  pintro
  exact true_intro

theorem contradiction : Γ ⊢ ~ p ⇒ p ⇒ q := by
  pintros
  papply false_elim
  papplya 1
  passumption

theorem double_neg : Γ ⊢ p ⇒ ~ ~ p := by
  pintros
  papplya 0
  passumption

theorem double_neg₂ : Γ ⊢ ~ ~ p ⇒ p := by
  pintro
  papply transpose
  · exact double_neg
  · passumption

theorem transpose₄ : Γ ⊢ (~ p ⇒ q) ⇒ ~ q ⇒ p := by
  papply composition
  · exact transpose₂
  · papply ax .imp_distrib
    pintro
    exact double_neg₂

theorem not_imp_left : Γ ⊢ ~ (p ⇒ q) ⇒ p := by
  pintro
  papply double_neg₂
  papply transpose₂
  · exact contradiction (q := q)
  · passumption

theorem not_imp_right : Γ ⊢ ~ (p ⇒ q) ⇒ ~ q := by
  papply transpose₂
  exact ax .imp_self

theorem and_intro : Γ ⊢ p ⇒ q ⇒ p ⩑ q := by
  pintros
  papplya 0 <;> passumption

theorem and_left : Γ ⊢ p ⩑ q ⇒ p := by
  pintro
  papply double_neg₂
  pintro
  papplya 1
  pintros
  papply false_elim
  papplya 2
  passumption

theorem and_right : Γ ⊢ p ⩑ q ⇒ q := by
  pintro
  papply double_neg₂
  pintro
  papplya 1
  pintro
  passumption

theorem or_inl : Γ ⊢ p ⇒ p ⩒ q := by
  pintros
  papply contradiction <;> passumption

theorem or_inr : Γ ⊢ q ⇒ p ⩒ q := ax .imp_self

theorem or_elim : Γ ⊢ p ⩒ q ⇒ (p ⇒ r) ⇒ (q ⇒ r) ⇒ r := by
  pintros
  papply double_neg₂
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

theorem excluded_middle : Γ ⊢ ~ p ⩒ p := double_neg₂

theorem andN_intro {v : Vec (𝓛.Formula n) m} :
  (∀ i, Γ ⊢ v i) → Γ ⊢ ⋀i, v i := by
  intro h
  induction m with
  | zero => exact true_intro
  | succ n ih =>
    papply and_intro
    · apply h
    · apply ih; intro i; apply h

theorem andN_elim {v : Vec (𝓛.Formula n) m} {i : Fin m} :
  (Γ ⊢ ⋀i, v i) → Γ ⊢ v i := by
  intro h
  induction m with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact mp and_left h
    | succ i => apply ih (mp and_right h)

theorem iff_intro : Γ ⊢ (p ⇒ q) ⇒ (q ⇒ p) ⇒ (p ⇔ q) := and_intro
theorem iff_mp : Γ ⊢ (p ⇔ q) ⇒ (p ⇒ q) := and_left
theorem iff_mpr : Γ ⊢ (p ⇔ q) ⇒ (q ⇒ p) := and_right
theorem iff_iff : Γ ⊢ p ⇔ q → (Γ ⊢ p ↔ Γ ⊢ q) := λ h => ⟨iff_mp.mp₂ h, iff_mpr.mp₂ h⟩

theorem iff_refl : Γ ⊢ p ⇔ p := mp₂ iff_intro identity identity

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

theorem iff_congr_neg : Γ ⊢ (p ⇔ q) ⇒ (~ p ⇔ ~ q) := by
  pintro
  papply iff_congr_imp
  · passumption
  · exact iff_refl

theorem double_neg_iff : Γ ⊢ ~ ~ p ⇔ p := iff_intro.mp₂ double_neg₂ double_neg

theorem iff_congr_forall : Γ ⊢ ∀' (p ⇔ q) ⇒ ∀' p ⇔ ∀' q := by
  pintro
  papply iff_intro <;> papply forall_imp <;> prevert <;> papply forall_imp <;> apply forall_intro
  · exact iff_mp
  · exact iff_mpr

theorem not_forall_iff : Γ ⊢ ~ ∀' p ⇔ ∃' (~ p) := iff_congr_neg.mp (iff_congr_forall.mp (forall_intro (iff_symm.mp double_neg_iff)))
theorem not_exists_iff : Γ ⊢ ~ ∃' p ⇔ ∀' (~ p) := double_neg_iff
theorem not_exists_not_iff : Γ ⊢ ~ ∃' (~ p) ⇔ ∀' p := iff_trans.mp₂ double_neg_iff (iff_congr_forall.mp (forall_intro double_neg_iff))

theorem exists_intro (t) : Γ ⊢ p[↦ₛ t]ₚ ⇒ ∃' p := by
  pintros
  suffices _ ⊢ (~ p)[↦ₛ t]ₚ by
    papply this
    passumption
  papply forall_elim
  passumption

theorem exists_elim : Γ ⊢ ∃' p ⇒ (∀' (p ⇒ ↑ₚq)) ⇒ q := by
  pintros
  papply double_neg₂
  pintros
  papplya 2
  suffices _ ⊢ ∀' (↑ₚ(~ q) ⇒ ~ p) by
    papply forall_imp
    · exact this
    · papply forall_self
      passumption
  papply forall_imp
  · apply forall_intro
    exact transpose₂
  · passumption

theorem exists_self : Γ ⊢ ∃' ↑ₚp ⇒ p := by
  papply transpose₄
  exact forall_self

theorem exists_imp : Γ ⊢ ∀' (p ⇒ q) ⇒ ∃' p ⇒ ∃' q := by
  pintros 2
  papply exists_elim
  · passumption 0
  · papply forall_imp (p := p ⇒ q)
    · apply forall_intro
      pintros 2
      papply exists_intro #0
      suffices _ ⊢ q by
        convert this
        rw [←Formula.subst_comp]; nth_rw 2 [←Formula.subst_id (p := q)]
        congr; funext x; cases x using Fin.cases <;> simp
      papplya 1
      passumption 0
    · passumption

theorem eq_refl : Γ ⊢ t ≐ t := ax .eq_refl
macro "prefl" : tactic => `(tactic| pexact eq_refl)

theorem eq_subst : Γ ⊢ t₁ ≐ t₂ ⇒ p[↦ₛ t₁]ₚ ⇒ p[↦ₛ t₂]ₚ := ax .eq_subst

theorem eq_symm : Γ ⊢ t₁ ≐ t₂ ⇒ t₂ ≐ t₁ := by
  have h := @eq_subst _ _ Γ t₁ t₂ (#0 ≐ ↑ₜt₁)
  simp [Term.shift_subst_single] at h
  pintro
  papply h
  · passumption
  · prefl
macro "psymm" : tactic => `(tactic| papply eq_symm)

theorem eq_trans : Γ ⊢ t₁ ≐ t₂ ⇒ t₂ ≐ t₃ ⇒ t₁ ≐ t₃ := by
  have h := @eq_subst _ _ Γ t₂ t₁ (#0 ≐ ↑ₜt₃)
  simp [Term.shift_subst_single] at h
  pintros
  papply h
  · psymm; passumption
  · passumption
macro "ptrans" t:(ppSpace colGt term)? : tactic =>
  match t with
  | some t => `(tactic| papply eq_trans (t₂ := $t))
  | none => `(tactic| papply eq_trans)

theorem eq_subst_iff : Γ ⊢ t₁ ≐ t₂ ⇒ p[↦ₛ t₁]ₚ ⇔ p[↦ₛ t₂]ₚ := by
  pintro
  papply iff_intro <;> papply eq_subst
  · passumption
  · psymm; passumption

theorem eq_subst_term : Γ ⊢ t₁ ≐ t₂ ⇒ t[↦ₛ t₁]ₜ ≐ t[↦ₛ t₂]ₜ := by
  pintro
  have h := @eq_subst _ _ Γ t₁ t₂ (↑ₜ(t[↦ₛ t₁]ₜ) ≐ t)
  simp [Term.shift_subst_single] at h
  papply h
  · passumption
  · prefl

theorem eq_congr_func {v₁ v₂ : Vec (𝓛.Term n) m} :
  Γ ⊢ (⋀i, v₁ i ≐ v₂ i) ⇒ f ⬝ₜ v₁ ≐ f ⬝ₜ v₂ := by
  pintro
  suffices ∀ k ≤ m, _ ⊢ f ⬝ₜ v₁ ≐ f ⬝ₜ (λ i => if i < k then v₂ i else v₁ i) by
    have := this m (by rfl)
    simp at this; exact this
  intros k h₁
  induction k with
  | zero => simp; prefl
  | succ k ih =>
    ptrans
    · exact ih (Nat.le_of_succ_le h₁)
    · let k' : Fin m := ⟨k, h₁⟩
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
      papply eq_subst_term
      apply andN_elim (v := λ i => v₁ i ≐ v₂ i)
      passumption

theorem eq_subst_term' (h : ∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) : Γ ⊢ t[σ₁]ₜ ≐ t[σ₂]ₜ := by
  induction t with simp
  | var => apply h
  | func f v ih => papply eq_congr_func; apply andN_intro; exact ih

theorem eq_congr_rel_iff {v₁ v₂ : Vec (𝓛.Term n) m} :
  Γ ⊢ (⋀i, v₁ i ≐ v₂ i) ⇒ r ⬝ᵣ v₁ ⇔ r ⬝ᵣ v₂ := by
  pintro
  suffices ∀ k ≤ m, _ ⊢ r ⬝ᵣ v₁ ⇔ r ⬝ᵣ (λ i => if i < k then v₂ i else v₁ i) by
    have := this m (by rfl)
    simp at this; exact this
  intros k h₁
  induction k with
  | zero => simp; exact iff_refl
  | succ k ih =>
    papply iff_trans
    · exact ih (Nat.le_of_succ_le h₁)
    · let k' : Fin m := ⟨k, h₁⟩
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
      papply eq_subst_iff
      apply andN_elim (v := λ i => v₁ i ≐ v₂ i)
      passumption

theorem eq_congr_rel {v₁ v₂ : Vec (𝓛.Term n) m} :
  Γ ⊢ (⋀i, v₁ i ≐ v₂ i) ⇒ r ⬝ᵣ v₁ ⇒ r ⬝ᵣ v₂ := by
  pintro
  papply iff_mp
  papply eq_congr_rel_iff
  passumption

theorem eq_congr_eq : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ ≐ t₂ ⇒ t₁' ≐ t₂' := by
  pintros
  ptrans
  · psymm; passumption
  · ptrans <;> passumption

theorem eq_congr_eq_iff : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ ≐ t₂ ⇔ t₁' ≐ t₂' := by
  pintros 2
  papply iff_intro
  · papply eq_congr_eq <;> passumption
  · papply eq_congr_eq <;> psymm <;> passumption

theorem eq_subst_iff' (h : ∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) : Γ ⊢ p[σ₁]ₚ ⇔ p[σ₂]ₚ := by
  induction p generalizing n with simp
  | rel r v =>
    papply eq_congr_rel_iff; apply andN_intro; intro; apply eq_subst_term'; exact h
  | eq t₁ t₂ =>
    papply eq_congr_eq_iff <;> apply eq_subst_term' <;> exact h
  | false =>
    exact iff_refl
  | imp p q ih₁ ih₂ =>
    papply iff_congr_imp <;> apply_assumption <;> exact h
  | all p ih =>
    papply iff_congr_forall; apply forall_intro; apply ih; intro i
    cases i using Fin.cases with simp
    | zero => prefl
    | succ i => apply shift (p := σ₁ i ≐ σ₂ i); apply h

theorem eq_subst' (h : ∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) : Γ ⊢ p[σ₁]ₚ ⇒ p[σ₂]ₚ := by
  papply iff_mp
  exact eq_subst_iff' h

namespace Rewrite

mutual
inductive Term (Γ : 𝓛.FormulaSet n) : 𝓛.Term n → 𝓛.Term n → Prop
| matched {t₁ t₂} : Γ ⊢ t₁ ≐ t₂ → Term Γ t₁ t₂
| func : Terms Γ v₁ v₂ → Term Γ (f ⬝ₜ v₁) (f ⬝ₜ v₂)
| refl {t} : Term Γ t t
inductive Terms (Γ : 𝓛.FormulaSet n) : Vec (𝓛.Term n) m → Vec (𝓛.Term n) m → Prop
| cons {t₁ t₂} : Term Γ t₁ t₂ → Terms Γ v₁ v₂ → Terms Γ (t₁ ∷ᵥ v₁) (t₂ ∷ᵥ v₂)
| refl : Terms Γ v v
end

theorem Terms.term :
  ∀ {m} {v₁ v₂ : Vec (𝓛.Term n) m}, Terms Γ v₁ v₂ → ∀ i, Term Γ (v₁ i) (v₂ i)
| _, _, _, cons h₁ h₂, i => i.cases h₁ (λ _ => h₂.term _)
| _, _, _, refl, _ => Term.refl

theorem Term.sound : ∀ {t₁ t₂}, Term Γ t₁ t₂ → Γ ⊢ t₁ ≐ t₂
| _, _, matched h => h
| _, _, func h => by papply eq_congr_func; apply andN_intro; intro i; exact (h.term i).sound
| _, _, refl => by prefl

inductive Formula (Γ : 𝓛.FormulaSet n) : 𝓛.Formula n → 𝓛.Formula n → Prop
| rel {r v₁ v₂} : Terms Γ v₁ v₂ → Formula Γ (r ⬝ᵣ v₁) (r ⬝ᵣ v₂)
| eq {t₁ t₁' t₂ t₂'} : Term Γ t₁ t₁' → Term Γ t₂ t₂' → Formula Γ (t₁ ≐ t₂) (t₁' ≐ t₂')
| imp {p₁ q₁ p₂ q₂} : Formula Γ p₁ q₁ → Formula Γ p₂ q₂ → Formula Γ (p₁ ⇒ p₂) (q₁ ⇒ q₂)
| refl {p} : Formula Γ p p

theorem Formula.sound : Formula Γ p q → Γ ⊢ p ⇔ q := by
  intro h
  induction h with
  | rel h => papply eq_congr_rel_iff; apply andN_intro; intro i; exact (h.term i).sound
  | eq => papply eq_congr_eq_iff <;> apply Term.sound <;> assumption
  | imp => papply iff_congr_imp <;> assumption
  | refl => exact iff_refl

macro "prewrite" t:term : tactic =>
  `(tactic| (
    apply mp₂ iff_mpr
    · apply Formula.sound
      repeat' first
      | apply Formula.rel | apply Formula.eq | apply Formula.imp | exact Formula.refl
      | apply Terms.cons | exact Terms.refl
      | exact Term.matched (by pexact $t) | apply Term.func | exact Term.refl
    try simp))

syntax rwRule := ("← "?) term

/--
  Rewrite goal using given terms.
  If a number `n` instead of a term is given, the `n`-th assumption will be used.
  
  Use `←` to change the direction. -/
elab "prw" "[" rules:withoutPosition(rwRule,*,?) "]" : tactic => do
  for rule in rules.raw.getSepArgs do
    let t ←
      match rule with
      | `(rwRule | $n:num) => Lean.Elab.liftMacroM (hypTerm n.getNat)
      | `(rwRule | $t:term) => pure t
      | `(rwRule | ← $n:num) => `(mp eq_symm $(← Lean.Elab.liftMacroM (hypTerm n.getNat)))
      | `(rwRule | ← $t:term) => `(mp eq_symm $t)
      | _ => throwError "unreachable"
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

namespace Theory

theorem generalization_alls : ↑ᴳ^[n] 𝓣 ⊢ p ↔ 𝓣 ⊢ ∀* p := by
  induction n with simp [Theory.shiftN, Formula.alls]
  | succ n ih => rw [Proof.generalization, ih]

theorem foralls_intro : ↑ᴳ^[n] 𝓣 ⊢ p → 𝓣 ⊢ ∀* p := generalization_alls.mp

theorem foralls_elim {σ : 𝓛.Subst n m} : 𝓣 ⊢ ∀* p → ↑ᴳ^[m] 𝓣 ⊢ p[σ]ₚ := by
  intro h
  induction n with simp [Formula.alls] at h
  | zero =>
    rw [Vec.eq_nil σ]; clear σ
    induction m with
    | zero => rw [←Vec.eq_nil Subst.id, Formula.subst_id]; exact h
    | succ m ih =>
      apply Proof.shift at ih
      simp [Formula.shift, ←Formula.subst_comp, Vec.eq_nil] at ih
      exact ih
  | succ n ih =>
    apply ih (σ := σ.tail) at h
    simp at h
    apply Proof.forall_elim (t := σ.head).mp at h
    rw [←Formula.subst_comp] at h
    convert h
    funext x; cases x using Fin.cases <;> simp [Vec.head, Term.shift_subst_single]

theorem foralls_imp : 𝓣 ⊢ ∀* (p ⇒ q) ⇒ ∀* p ⇒ ∀* q := by
  pintros
  apply foralls_intro
  apply Proof.mp (p := p) <;> rw [generalization_alls] <;> passumption

theorem iff_congr_foralls : 𝓣 ⊢ ∀* (p ⇔ q) ⇒ ∀* p ⇔ ∀* q := by
  pintro
  papply Proof.iff_intro <;> papply foralls_imp <;> papply foralls_intro
  · papply Proof.iff_mp; rw [generalization_alls]; passumption
  · papply Proof.iff_mpr; rw [generalization_alls]; passumption

end Theory

notation Γ:50 "⊬" p:50 => ¬ Γ ⊢ p

def Consistent (Γ : 𝓛.FormulaSet n) := Γ ⊬ ⊥

theorem Consistent.weaken : Γ ⊆ Δ → Consistent Δ → Consistent Γ := by
  intros h₁ h₂ h
  apply h₂
  exact Proof.weaken h₁ h

theorem Consistent.append : Consistent (Γ,' p) ↔ Γ ⊬ ~ p := by
  constructor
  · intro h₁ h₂
    apply h₁
    prevert
    exact h₂
  · intro h₁ h₂
    apply h₁
    pintro
    exact h₂

theorem Consistent.append_neg : Consistent (Γ,' ~ p) ↔ Γ ⊬ p := by
  constructor
  · intro h₁ h₂
    apply h₁
    prevert
    papply Proof.double_neg
    exact h₂
  · intro h₁ h₂
    apply h₁
    papply Proof.double_neg₂
    pintro
    exact h₂

def Complete (Γ : 𝓛.FormulaSet n) := ∀ p, Γ ⊢ p ∨ Γ ⊢ ~ p

theorem Complete.unprovable (h : Complete Γ) : Γ ⊬ p → Γ ⊢ ~ p := by
  rcases h p with h₁ | h₁ <;> simp [h₁]

theorem Complete.unprovable_iff (h₁ : Complete Γ) (h₂ : Consistent Γ) : Γ ⊬ p ↔ Γ ⊢ ~ p := by
  rcases h₁ p with h | h <;> simp [h] <;> intro h'
  · exact h₂ (h'.mp h)
  · exact h₂ (h.mp h')

def Henkin (Γ : 𝓛.FormulaSet n) := ∀ p, Γ ⊢ ∃' p → ∃ (c : 𝓛.Const), Γ ⊢ p[↦ₛ c]ₚ

end FirstOrder.Language
