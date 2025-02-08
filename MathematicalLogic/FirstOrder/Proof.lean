import Mathlib.Data.Set.Finite.Basic
import MathematicalLogic.FirstOrder.Syntax
import MathematicalLogic.FirstOrder.Proof.Init

namespace FirstOrder.Language

inductive Axiom (𝓛 : Language) : 𝓛.FormulaSet n where
| imp_self : 𝓛.Axiom (p ⇒ q ⇒ p)
| imp_distrib : 𝓛.Axiom ((p ⇒ q ⇒ r) ⇒ (p ⇒ q) ⇒ p ⇒ r)
| transpose : 𝓛.Axiom ((~ p ⇒ ~ q) ⇒ q ⇒ p)
| forall_elim : 𝓛.Axiom (∀' p ⇒ p[↦ₛ t]ₚ)
| forall_self : 𝓛.Axiom (p ⇒ ∀' ↑ₚp)
| forall_imp : 𝓛.Axiom (∀' (p ⇒ q) ⇒ ∀' p ⇒ ∀' q)
| eq_refl : 𝓛.Axiom (t ≐ t)
| eq_symm : 𝓛.Axiom (t₁ ≐ t₂ ⇒ t₂ ≐ t₁)
| eq_trans : 𝓛.Axiom (t₁ ≐ t₂ ⇒ t₂ ≐ t₃ ⇒ t₁ ≐ t₃)
| eq_congr_func : 𝓛.Axiom ((⋀ i, v₁ i ≐ v₂ i) ⇒ f ⬝ᶠ v₁ ≐ f ⬝ᶠ v₂)
| eq_congr_rel : 𝓛.Axiom ((⋀ i, v₁ i ≐ v₂ i) ⇒ r ⬝ʳ v₁ ⇒ r ⬝ʳ v₂)
| all : 𝓛.Axiom p → 𝓛.Axiom (∀' p)

variable {𝓛 : Language}

theorem Axiom.subst {σ : 𝓛.Subst n m} : p ∈ 𝓛.Axiom → p[σ]ₚ ∈ 𝓛.Axiom := by
  intro h
  induction h generalizing m <;> simp [Term.shift_subst_lift, Formula.shift_subst_lift, Formula.subst_swap_single, Formula.subst_andN]
  case all ih => exact all ih
  all_goals constructor

inductive Proof (Γ : 𝓛.FormulaSet n) : 𝓛.Formula n → Prop where
| hyp : p ∈ Γ → Proof Γ p
| ax : p ∈ 𝓛.Axiom → Proof Γ p
| mp : Proof Γ (p ⇒ q) → Proof Γ p → Proof Γ q
infix:50 " ⊢ " => Proof

namespace Proof

variable {n} {Γ : 𝓛.FormulaSet n}

theorem hyp_append : Γ,' p ⊢ p := hyp FormulaSet.mem_append

theorem weaken : Γ ⊆ Δ → Γ ⊢ p → Δ ⊢ p := by
  intros h₁ h₂
  induction h₂ with
  | hyp h => exact hyp (h₁ h)
  | ax h => exact ax h
  | mp _ _ ih₁ ih₂ => exact mp ih₁ ih₂

theorem weaken_append : Γ ⊢ p → Γ,' q ⊢ p := weaken FormulaSet.subset_append

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

theorem shiftN : Γ ⊢ p → ↑ᴳ^[m] Γ ⊢ ↑ₚ^[m] p := by
  intro h
  induction m with
  | zero => exact h
  | succ m ih => exact shift ih

theorem forall_imp : Γ ⊢ ∀' (p ⇒ q) ⇒ ∀' p ⇒ ∀' q := ax .forall_imp
theorem forall_elim (t) : Γ ⊢ ∀' p ⇒ p[↦ₛ t]ₚ := ax .forall_elim
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
    apply (forall_elim #0).mp at h
    rw [←Formula.subst_comp, Subst.lift_comp_single, ←Subst.assign, Subst.assign_zero, Formula.subst_id] at h
    exact h

theorem forall_intro : ↑ᴳΓ ⊢ p → Γ ⊢ ∀' p := generalization.mp

namespace Tactics

open Lean Meta Elab Tactic

/--
  Introduce a new hypothesis through deduction theorem, or introduce a new variable through generalization theorem. -/
macro "pintro" : tactic => `(tactic|
  first
  | apply deduction.mpr
  | (apply forall_intro; try simp only [FormulaSet.shift_append, FormulaSet.shiftN_append, Theory.shift_shiftN, Theory.shiftN_shiftN]))

/-- Revert a hypothesis through deduction theorem. -/
macro "prevert" : tactic => `(tactic| apply deduction.mp)

/-- Repeatly introduce new hypotheses and variables. Use `pintros n` to contol the number of hypothesis introduced. -/
macro "pintros" n:(ppSpace colGt num)? : tactic =>
  match n with
  | some n => `(tactic| iterate $n pintro)
  | none => `(tactic| repeat pintro)

private def hypTerm (n : ℕ) : MacroM (Lean.TSyntax `term) := do
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

/-- For goal `Γ ⊢ p`, `phave q` proves `Γ ⊢ q` first and then proves `Γ, q ⊢ p`. -/
macro "phave" t:(ppSpace colGt term) : tactic =>
  `(tactic| refine cut (p := $t) ?_ ?_)

/-- For goal `Γ ⊢ p`, `psuffices q` proves `Γ, q ⊢ p` first and then proves `Γ ⊢ q`. -/
macro "psuffices" t:(ppSpace colGt term) : tactic =>
  `(tactic| (refine cut (p := $t) ?_ ?_; swap))

/-- Remove the `n`-th assumption. -/
macro "pclear" n:(ppSpace colGt num) : tactic => do
  let mut weakenTerm ← `(FormulaSet.subset_append)
  for _ in [:n.getNat] do
    weakenTerm ← `(FormulaSet.append_subset_append $weakenTerm)
  `(tactic| apply weaken $weakenTerm)

/-- Remove all assumptions except the `FormulaSet`. -/
macro "pclears" : tactic => `(tactic| repeat apply weaken_append)

/-- Unify `Γ ⊆ Δ` as `Γ, p₁, ⋯, pₙ = Δ`. Return `some n` if succeed, and `none` if fail. -/
private partial def isSubsetOf (Γ Δ : Expr) : MetaM (Option ℕ) := do
  let s ← MonadBacktrack.saveState
  if ← isDefEq Γ Δ then
    return some 0
  MonadBacktrack.restoreState s
  if let some (_, _, Δ', _) := Δ.app4? ``FormulaSet.append then
    if let some n := ← isSubsetOf Γ Δ' then
      return some (n + 1)
  return none

/--
  Given a proof term `t` of `Γ ⊢ p₁ ⇒ ⋯ ⇒ pₙ`, `papply t` apply it on the current goal `Δ ⊢ pₙ` using MP.
  The main goal becomes `Δ ⊢ p₁`, and 
  `Γ` should be a subset of `Δ`.
  
  Control the application depth `n` through `with` clause. -/
elab "papply" t:(ppSpace colGt term) d:((" with " num)?) : tactic =>
  withMainContext do
    let appTerm ← Term.elabTerm t none
    let appType ← instantiateMVars (← Lean.Meta.inferType appTerm)
    let (forallMVars, _, type) ← forallMetaTelescopeReducing appType
    let (mkApp4 (.const ``Proof []) 𝓛 n Γ p) := type
      | throwError m!"{type} is not a proof"
    let goal ← getMainGoal
    let goalType ← goal.getType'
    let some (𝓛', m, Δ, _) := goalType.app4? ``Proof
      | throwError m!"{goalType} is not a proof"
    let true := ← isDefEq n m
      | throwError m!"failed to unify {n} and {m}"
    let true := ← isDefEq 𝓛 𝓛'
      | throwError m!"failed to unify {𝓛} and {𝓛'}"
    let some weakenDepth := ← isSubsetOf Γ Δ
      | throwError m!"failed to unify {Γ} as a subset of {Δ}"
    let weakenTy ← do
      let weakenTy := mkApp3 (.const ``Set.Subset [0]) (mkApp2 (.const ``Formula []) 𝓛 n) Γ Δ
      pure weakenTy
    let weakenTerm ← do
      let mut weakenTerm ← `(Set.Subset.refl _)
      for _ in [:weakenDepth] do
        weakenTerm := ← `(Set.Subset.trans $weakenTerm FormulaSet.subset_append)
      elabTerm weakenTerm (some weakenTy)
    let mut proofTerm := mkApp7
      (.const ``weaken []) 𝓛 n Γ Δ p weakenTerm
      (mkAppN appTerm forallMVars)
    let mut newMVarIds := []
    let mut goalFormula := p
    let maxDepth := d.raw.getArgs[1]?.map (·.toNat)
    repeat do
      let proofType ← inferType proofTerm
      if !maxDepth.any (λ d => newMVarIds.length < d) then
        let s ← MonadBacktrack.saveState
        if ← isDefEq goalType proofType then
          goal.assign proofTerm
          break
        if maxDepth.any λ d => newMVarIds.length >= d then
          throwError "failed to apply {appType} at {goalType} within depth {maxDepth.get!}"
        MonadBacktrack.restoreState s
      if let some (_, _, p, q) := (← whnf goalFormula).app4? ``Formula.imp then
        let mvarId ← mkFreshMVarId
        newMVarIds := newMVarIds ++ [mvarId]
        let mvar ← mkFreshExprMVarWithId mvarId (some (mkApp4 (.const ``Proof []) 𝓛 n Δ p))
        proofTerm := mkApp7 (.const ``mp []) 𝓛 n Δ p q proofTerm mvar
        goalFormula := q
      else
        throwError "failed to apply {appType} at {goalType}"
    for mvar in forallMVars do
      if let (.mvar mvarid) := mvar then
        if !(← mvarid.isAssigned) then
          newMVarIds := newMVarIds ++ [mvarid]
    replaceMainGoal newMVarIds

/-- Apply the `n`-th assumption through MP. -/
macro "papplya" n:(ppSpace colGt num) : tactic => do
  `(tactic| papply $(← hypTerm n.getNat))

/-- Close the goal with given proof term. -/
macro "pexact" t:(ppSpace colGt term) : tactic =>
  `(tactic| papply $t with 0)

end Tactics

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
  (∀ i, Γ ⊢ v i) → Γ ⊢ ⋀ i, v i := by
  intro h
  induction m with
  | zero => exact true_intro
  | succ n ih =>
    papply and_intro
    · apply h
    · apply ih; intro i; apply h

theorem andN_elim {v : Vec (𝓛.Formula n) m} {i : Fin m} :
  (Γ ⊢ ⋀ i, v i) → Γ ⊢ v i := by
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
      rw [←Formula.subst_comp, Subst.lift_comp_single, ←Subst.assign, Subst.assign_zero, Formula.subst_id]
      papplya 1
      passumption 0
    · passumption

theorem forallN_intro : ↑ᴳ^[m] Γ ⊢ p → Γ ⊢ ∀^[m] p := by
  intro h
  induction m with simp [FormulaSet.shiftN, Formula.allN] at *
  | zero => exact h
  | succ m ih => apply ih; pintro; exact h

theorem forallN_elim' (σ₁) : Γ ⊢ (∀^[m] p)[σ₂]ₚ ⇒ p[σ₁ ++ᵥ σ₂]ₚ := by
  induction m with simp [Formula.allN]
  | zero =>
    simp [Vec.eq_nil]; exact identity
  | succ m ih =>
    rw [Vec.eq_cons σ₁]; simp
    pintro
    rw [←Subst.lift_comp_single, Formula.subst_comp]
    papply forall_elim σ₁.head
    rw [←Formula.subst_all]
    papply ih (σ₁.tail)
    passumption

theorem forallN_elim  (σ) : Γ ⊢ ∀^[m] p ⇒ p[σ ++ᵥ Subst.id]ₚ := by
  rw [←Formula.subst_id (∀^[m] p)]
  apply forallN_elim'

theorem forallN_imp : Γ ⊢ ∀^[m] p ⇒ ∀^[m] (p ⇒ q) ⇒ ∀^[m] q := by
  pintros
  apply forallN_intro
  simp [Formula.shiftN_eq_subst]
  apply mp (p := p)
  · nth_rw 2 [←Formula.subst_id (p ⇒ q)]
    rw [←Subst.castAdd'_append_addNat]
    papply forallN_elim'
    passumption
  · nth_rw 3 [←Formula.subst_id p]
    rw [←Subst.castAdd'_append_addNat]
    papply forallN_elim'
    passumption

theorem existsN_intro' {p : 𝓛.Formula (k + m)} (σ₁) : Γ ⊢ p[σ₁ ++ᵥ σ₂]ₚ ⇒ (∃^[m] p)[σ₂]ₚ := by
  induction m with simp [Formula.exN]
  | zero =>
    simp [Vec.eq_nil]; exact identity
  | succ m ih =>
    rw [Vec.eq_cons σ₁]; simp
    pintro
    papply ih σ₁.tail
    papply exists_intro σ₁.head
    rw [←Formula.subst_comp, Subst.lift_comp_single]
    passumption

theorem existsN_intro {p : 𝓛.Formula (n + m)} (σ) :
  Γ ⊢ p[σ ++ᵥ Subst.id]ₚ ⇒ ∃^[m] p := by
  rw [←Formula.subst_id (∃^[m] p)]
  apply existsN_intro'

theorem existsN_elim {p : 𝓛.Formula (n + m)} :
  Γ ⊢ ∃^[m] p ⇒ ∀^[m] (p ⇒ ↑ₚ^[m] q) ⇒ q := by
  induction m with simp [Formula.exN, Formula.allN]
  | zero =>
    pintros; papplya 0; passumption
  | succ m ih =>
    pintros
    papply ih (p := ∃' p)
    · passumption
    · papply forallN_imp
      · passumption 0
      · apply forallN_intro
        pintros
        papply exists_elim <;> passumption

theorem eq_refl : Γ ⊢ t ≐ t := ax .eq_refl

/-- Close the proof goal `t ≐ t` or `p ⇔ p` using reflexitivity. -/
macro "prefl" : tactic => `(tactic| first | pexact eq_refl | pexact iff_refl)

theorem eq_symm : Γ ⊢ t₁ ≐ t₂ ⇒ t₂ ≐ t₁ := ax .eq_symm

/-- If the proof goal is `t₁ ≐ t₂` or `p ⇔ q`, replace it with `t₂ ≐ t₁` or `q ⇔ p` using symmetry. -/
macro "psymm" : tactic => `(tactic| first | papply eq_symm | papply iff_symm)

theorem eq_trans : Γ ⊢ t₁ ≐ t₂ ⇒ t₂ ≐ t₃ ⇒ t₁ ≐ t₃ := ax .eq_trans

/--
  If the proof goal is `t₁ ≐ t₂` (or `p ⇔ q`), replace it with two goals,
  `t₁ ≐ t` and `t ≐ t` (or `p ⇔ r` and `r ⇔ q`) using transtivity.
  
  A meta variable is generated for `t` or `r` if it is not given. -/
macro "ptrans" t:(ppSpace colGt term)? : tactic =>
  match t with
  | some t => `(tactic| first | papply eq_trans (t₂ := $t) | papply iff_trans (q := $t))
  | none => `(tactic| first | papply eq_trans | papply iff_trans)

theorem eq_congr_func : Γ ⊢ (⋀ i, v₁ i ≐ v₂ i) ⇒ f ⬝ᶠ v₁ ≐ f ⬝ᶠ v₂ := ax .eq_congr_func

theorem eq_subst_term (h : ∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) : Γ ⊢ t[σ₁]ₜ ≐ t[σ₂]ₜ := by
  induction t with simp
  | var => apply h
  | func f v ih => papply eq_congr_func; apply andN_intro; exact ih

theorem eq_subst_term_single : Γ ⊢ t₁ ≐ t₂ ⇒ t[↦ₛ t₁]ₜ ≐ t[↦ₛ t₂]ₜ := by
  pintro
  apply eq_subst_term
  intro i
  cases i using Fin.cases with simp
  | zero => passumption
  | succ i => prefl

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

theorem eq_congr_rel : Γ ⊢ (⋀ i, v₁ i ≐ v₂ i) ⇒ r ⬝ʳ v₁ ⇒ r ⬝ʳ v₂ := ax .eq_congr_rel

theorem eq_congr_rel_iff : Γ ⊢ (⋀ i, v₁ i ≐ v₂ i) ⇒ r ⬝ʳ v₁ ⇔ r ⬝ʳ v₂ := by
  pintro
  papply iff_intro <;> papply eq_congr_rel
  · passumption
  · apply andN_intro
    intro i
    psymm
    papply andN_elim (v := λ i => v₁ i ≐ v₂ i)
    passumption

theorem eq_subst_iff (h : ∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) : Γ ⊢ p[σ₁]ₚ ⇔ p[σ₂]ₚ := by
  induction p generalizing n with simp
  | rel r v =>
    papply eq_congr_rel_iff; apply andN_intro; intro; apply eq_subst_term; exact h
  | eq t₁ t₂ =>
    papply eq_congr_eq_iff <;> apply eq_subst_term <;> exact h
  | false =>
    exact iff_refl
  | imp p q ih₁ ih₂ =>
    papply iff_congr_imp <;> apply_assumption <;> exact h
  | all p ih =>
    papply iff_congr_forall; apply forall_intro; apply ih; intro i
    cases i using Fin.cases with simp
    | zero => prefl
    | succ i => apply shift (p := σ₁ i ≐ σ₂ i); apply h

theorem eq_subst_single_iff : Γ ⊢ t₁ ≐ t₂ ⇒ p[↦ₛ t₁]ₚ ⇔ p[↦ₛ t₂]ₚ := by
  pintro
  apply eq_subst_iff
  intro i
  cases i using Fin.cases with simp
  | zero => passumption
  | succ i => prefl

theorem eq_subst (h : ∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) : Γ ⊢ p[σ₁]ₚ ⇒ p[σ₂]ₚ := by
  papply iff_mp
  exact eq_subst_iff h

theorem eq_subst_single : Γ ⊢ t₁ ≐ t₂ ⇒ p[↦ₛ t₁]ₚ ⇒ p[↦ₛ t₂]ₚ := by
  pintro
  papply iff_mp
  papply eq_subst_single_iff
  passumption

def RwTerm (Γ : 𝓛.FormulaSet n) (t₁ t₂ : 𝓛.Term n) := Γ ⊢ t₁ ≐ t₂
def RwTermVec (Γ : 𝓛.FormulaSet n) (v₁ v₂ : Vec (𝓛.Term n) m) := ∀ i, RwTerm Γ (v₁ i) (v₂ i)
def RwFormula (Γ : 𝓛.FormulaSet n) (p q : 𝓛.Formula n) := Γ ⊢ p ⇔ q

theorem RwTerm.matched : Γ ⊢ t₁ ≐ t₂ → RwTerm Γ t₁ t₂ := id

@[prw] theorem RwTerm.func : RwTermVec Γ v₁ v₂ → RwTerm Γ (f ⬝ᶠ v₁) (f ⬝ᶠ v₂) := by
  intro h
  papply eq_congr_func
  exact andN_intro h

theorem RwTerm.refl : RwTerm Γ t t := by prefl

@[prw] theorem RwTermVec.cons : RwTerm Γ t₁ t₂ → RwTermVec Γ v₁ v₂ → RwTermVec Γ (t₁ ∷ᵥ v₁) (t₂ ∷ᵥ v₂) := by
  intro h₁ h₂ i
  exact i.cases h₁ h₂

theorem RwTermVec.refl : RwTermVec Γ v v := by intro; prefl

theorem RwFormula.matched : Γ ⊢ p ⇔ q → RwFormula Γ p q := id

@[prw] theorem RwFormula.rel : RwTermVec Γ v₁ v₂ → RwFormula Γ (r ⬝ʳ v₁) (r ⬝ʳ v₂) := by
  intro h
  papply eq_congr_rel_iff
  exact andN_intro h

@[prw] theorem RwFormula.eq : RwTerm Γ t₁ t₁' → RwTerm Γ t₂ t₂' → RwFormula Γ (t₁ ≐ t₂) (t₁' ≐ t₂') := by
  intros
  papply eq_congr_eq_iff <;> assumption

@[prw] theorem RwFormula.imp : RwFormula Γ p p' → RwFormula Γ q q' → RwFormula Γ (p ⇒ q) (p' ⇒ q') := by
  intros
  papply iff_congr_imp <;> assumption

theorem RwFormula.refl : RwFormula Γ p p := by prefl
 
@[prw] theorem RwFormula.neg : RwFormula Γ p q → RwFormula Γ (~ p) (~ q) := (imp · refl)

@[prw] theorem RwFormula.and : RwFormula Γ p₁ q₁ → RwFormula Γ p₂ q₂ → RwFormula Γ (p₁ ⩑ p₂) (q₁ ⩑ q₂) :=
  λ h₁ h₂ => neg (imp h₁ (neg h₂))

@[prw] theorem RwFormula.or : RwFormula Γ p₁ q₁ → RwFormula Γ p₂ q₂ → RwFormula Γ (p₁ ⩒ p₂) (q₁ ⩒ q₂) :=
  λ h₁ h₂ => imp (neg h₁) h₂

@[prw] theorem RwFormula.iff : RwFormula Γ p₁ q₁ → RwFormula Γ p₂ q₂ → RwFormula Γ (p₁ ⇔ p₂) (q₁ ⇔ q₂) :=
  λ h₁ h₂ => and (imp h₁ h₂) (imp h₂ h₁)

namespace Tactics

syntax rwRule := ("← "?) term

open Lean Meta Elab Tactic

/--
  Rewrite goal using given terms.
  If a number `n` instead of a term is given, the `n`-th assumption will be used.
  
  Use `←` to change the direction. -/
elab "prw" "[" rules:withoutPosition(rwRule,*,?) "]" : tactic => do
  for rule in rules.raw.getSepArgs do
    let t ← match rule with
      | `(rwRule | $n:num) =>
        let t ← Lean.Elab.liftMacroM (hypTerm n.getNat)
        `(tacticSeq | pexact $t)
      | `(rwRule | $t:term) => `(tacticSeq | pexact $t)
      | `(rwRule | ← $n:num) =>
        let t ← Lean.Elab.liftMacroM (hypTerm n.getNat)
        `(tacticSeq | psymm; pexact $t)
      | `(rwRule | ← $t:term) => `(tacticSeq | psymm; pexact $t)
      | _ => throwError "unreachable"
    evalTactic (←`(tactic| apply mp₂ iff_mpr))
      let arr := (prwExt.getState (← MonadEnv.getEnv)).reverse
    let newGoals ← repeat'
      λ goal => do
        evalTacticAt (←`(tactic| first | apply RwTerm.matched; ($t) | apply RwFormula.matched; ($t))) goal
          <|> arr.foldl
            (λ tac e => tac <|> do (evalTacticAt (←`(tactic| apply $(mkIdent e))) goal))
            failure
          <|> evalTacticAt (←`(tactic| first
            | exact RwTerm.refl | exact RwTermVec.refl | exact RwFormula.refl)) goal
      ([← getMainGoal])
    appendGoals newGoals

end Tactics

theorem ne_symm : Γ ⊢ ~ t₁ ≐ t₂ ⇒ ~ t₂ ≐ t₁ := by
  pintros
  papplya 1
  prw [0]
  prefl

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

variable {𝓣 : 𝓛.Theory}

theorem generalization_alls : ↑ᵀ^[n] 𝓣 ⊢ p ↔ 𝓣 ⊢ ∀* p := by
  induction n with simp [Formula.alls]
  | zero => rfl
  | succ n ih => rw [←Theory.shift_shiftN, Proof.generalization, ih]

theorem foralls_intro : ↑ᵀ^[n] 𝓣 ⊢ p → 𝓣 ⊢ ∀* p := generalization_alls.mp

theorem foralls_elim (σ : 𝓛.Subst n m) : 𝓣 ⊢ ∀* p → ↑ᵀ^[m] 𝓣 ⊢ p[σ]ₚ := by
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
    apply (Proof.forall_elim σ.head).mp at h
    rw [←Formula.subst_comp, Subst.lift_comp_single, ←Vec.eq_cons] at h
    exact h

theorem foralls_imp : 𝓣 ⊢ ∀* (p ⇒ q) ⇒ ∀* p ⇒ ∀* q := by
  pintros
  apply foralls_intro
  apply Proof.mp (p := p) <;> rw [generalization_alls] <;> passumption

theorem iff_congr_foralls : 𝓣 ⊢ ∀* (p ⇔ q) ⇒ ∀* p ⇔ ∀* q := by
  pintro
  papply Proof.iff_intro <;> papply foralls_imp <;> papply foralls_intro
  · papply Proof.iff_mp; rw [generalization_alls]; passumption
  · papply Proof.iff_mpr; rw [generalization_alls]; passumption

abbrev theorems (𝓣 : 𝓛.Theory) : 𝓛.Theory := { p | 𝓣 ⊢ p }

abbrev Decidable (𝓣 : 𝓛.Theory) := DecidablePred 𝓣.theorems

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
