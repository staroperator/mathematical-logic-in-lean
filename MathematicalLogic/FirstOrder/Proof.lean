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

open Lean Syntax Meta Elab Tactic

/-- Introduce a new hypothesis through `Proof.deduction`, or introduce a new variable through `Proof.forall_intro`. -/
macro "pintro" : tactic => `(tactic|
  first
  | eapply deduction.mpr
  | (eapply forall_intro; try simp only [FormulaSet.shift_append, FormulaSet.shiftN_append]))

/-- Revert a hypothesis through deduction theorem. -/
macro "prevert" : tactic => `(tactic| eapply deduction.mp)

/-- Repeatly introduce new hypotheses and variables. Use `pintros n` to contol the number of hypothesis introduced. -/
macro "pintros" n:(ppSpace colGt num)? : tactic =>
  match n with
  | some n => `(tactic| iterate $n pintro)
  | none => `(tactic| repeat pintro)

private def hypTerm (n : ℕ) : MacroM (TSyntax `term) := do
  let mut t ← `(hyp_append)
  for _ in [:n] do
    t ← `(weaken_append $t)
  return t

/--
  Close the proof goal using assumption.
  If a number `n` is given, the `n`-th assumption (from right to left) will be used.
  Otherwise, this tactic will try to search for such an assumption.
  -/
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
elab "pclear" n:(ppSpace colGt num) : tactic => do
  let mut weakenTerm ← `(FormulaSet.subset_append)
  for _ in [:n.getNat] do
    weakenTerm ← `(FormulaSet.append_subset_append $weakenTerm)
  let mainGoal :: _ ← evalTacticAt (← `(tactic| eapply weaken $weakenTerm)) (← getMainGoal) | throwError "pclear failed"
  replaceMainGoal [mainGoal]

/-- Remove all assumptions except the `FormulaSet`. -/
macro "pclears" : tactic => `(tactic| repeat apply pclear 0)

/-- Swap the `n`-th assumption and the `m`-th assumption. -/
elab "pswap" n:num m:num : tactic => do
  let mut n := n.getNat
  let mut m := m.getNat
  if n = m then return
  if n > m then (n, m) := (m, n)
  let mut permuteTerm ← `(Eq.refl _)
  for _ in [:m-n-1] do
    permuteTerm ← `(FormulaSet.append_eq_append (Eq.trans $permuteTerm FormulaSet.append_comm))
  permuteTerm ← `(Eq.trans $permuteTerm (Eq.trans FormulaSet.append_comm (Eq.symm $permuteTerm)))
  for _ in [:n] do
    permuteTerm ← `(FormulaSet.append_eq_append $permuteTerm)
  let mainGoal :: _ ← evalTacticAt (← `(tactic| eapply weaken (FormulaSet.subset_of_eq $permuteTerm))) (← getMainGoal)
    | throwError "pswap failed"
  replaceMainGoal [mainGoal]

/-- Replaces the `n`-th assumption with a new propositon, and generate a new goal to prove `Γ, ⋯ ⊢ p`. -/
macro "preplace" n:num t:term : tactic =>
  `(tactic| (psuffices $t; focus (pswap 0 $(mkNatLit (n.getNat+1)); pclear 0)))

/-- Unify `Γ ⊆ Δ` as `Γ, p₁, ⋯, pₙ = Δ`. Return `some t` (`t` is a syntax term of type `Γ ⊆ Δ`) if succeed, and `none` if fail. -/
private partial def isSubsetOf (Γ Δ : Expr) : MetaM (Option (TSyntax `term)) := do
  let s ← MonadBacktrack.saveState
  if ← isDefEq Γ Δ then
    return some (← `(Set.Subset.refl _))
  MonadBacktrack.restoreState s
  if let some (_, _, Δ', _) := Δ.app4? ``FormulaSet.append then
    if let some t ← isSubsetOf Γ Δ' then
      return some (← `(Set.Subset.trans $t FormulaSet.subset_append))
  return none

/--
  `f` should be a term of type `Γ ⊢ p₁ ⇒ p₂ ⇒ ⋯ ⇒ pₙ`, and `goal` should be a type `Δ ⊢ pₙ` (in whnf) where `Γ ⊆ Δ`.
  
  `apply f goal d` will create a term `Proof.mp (Proof.mp (... (Proof.mp f ?m₁)) ?mₙ₋₂) ?mₙ₋₁` of type `goal`,
  return the term and a list of `?m₁, ⋯, ?mₙ₋₁`.
  -/
private def papply (f : Expr) (goal : Expr) (d : Option ℕ) : TacticM (Expr × List MVarId) := do
  let (fmvars, _, ftype) ← forallMetaTelescopeReducing (← instantiateMVars (← inferType f))
  let some (𝓛, n, Γ, p) := ftype.app4? ``Proof | throwError m!"{ftype} is not a proof"
  let some (𝓛', n', Δ, _) := goal.app4? ``Proof | throwError m!"{goal} is not a proof"
  let true := ← isDefEq 𝓛 𝓛' | throwError m!"failed to unify {𝓛} and {𝓛'}"
  let true := ← isDefEq n n' | throwError m!"failed to unify {n} and {n'}"
  let some weakenTerm := ← isSubsetOf Γ Δ | throwError m!"failed to unify {Γ} as a subset of {Δ}"
  let weakenTerm ←
    elabTermEnsuringType weakenTerm (some (mkApp3 (.const ``Set.Subset [0]) (mkApp2 (.const ``Formula []) 𝓛 n) Γ Δ)) true
  let mut proofTerm := mkApp7 (.const ``weaken []) 𝓛 n Γ Δ p weakenTerm (mkAppN f fmvars)
  let mut newMVarIds := []
  let mut goalFormula := p
  repeat do
    let proofType ← inferType proofTerm
    if d.all λ d => newMVarIds.length == d then
      let s ← MonadBacktrack.saveState
      if ← isDefEq goal proofType then
        break
      if d == some newMVarIds.length then
        throwError "failed to apply {ftype} at {goal} with depth {newMVarIds.length}"
      MonadBacktrack.restoreState s
    if let some (_, _, p, q) := (← whnf goalFormula).app4? ``Formula.imp then
      let mvarId ← mkFreshMVarId
      newMVarIds := newMVarIds ++ [mvarId]
      let mvar ← mkFreshExprMVarWithId mvarId (some (mkApp4 (.const ``Proof []) 𝓛 n Δ p))
      proofTerm := mkApp7 (.const ``mp []) 𝓛 n Δ p q proofTerm mvar
      goalFormula := q
    else
      throwError "failed to apply {ftype} at {goal}"
  for mvar in fmvars do
    if !(← mvar.mvarId!.isAssigned) then
      newMVarIds := newMVarIds ++ [mvar.mvarId!]
  return (proofTerm, newMVarIds)

syntax location := "at" (ident <|> num)

syntax depth := "with" num

/--
  Given a proof term `t` of `Γ ⊢ p₁ ⇒ ⋯ ⇒ pₙ ⇒ q`, `papply t` apply it on another goal using a chain
  of `Proof.mp`.
  - `papply t` will apply `t` on the current goal `Δ ⊢ q` (where `Γ` is a subset of `Δ`) and create
    goals for `Δ ⊢ pᵢ`.
  - `papply t at h` (where `h` is an identifier) will apply `t` on the local hypothesis `h` with
    type `Δ ⊢ pₙ` (where `Γ`
    is a subset of `Δ`), replace it with `Δ ⊢ q` and create goals for other `Δ ⊢ pᵢ`.
  - `papply t at k` (where `k` is an number literal) will apply `t` on the `k`-th assumption `pₙ` in
    current goal (on the LHS of `⊢`, counting from right to left), replace it with `q` and create
    goals for other `Δ ⊢ pᵢ`.
  
  `papply ⋯ with d` controls the number of `Proof.mp` (equal to `n`) to be `d`. If `with` is not
  presented, `papply` will try from `n = 0` until it succeeds or exhausts all `Proof.mp`.
  -/
elab "papply" t:(ppSpace colGt term) l:(location)? d:(depth)? : tactic => withMainContext do
  let d := d.map λ d => d.raw[1].toNat
  match l with
  | none =>
    let mainGoal ← getMainGoal
    let (goalTerm, newGoals) ← papply (← elabTerm t none true) (← mainGoal.getType') d
    mainGoal.assign goalTerm
    replaceMainGoal newGoals
  | some l =>
    if l.raw[1].getKind == identKind then
      let target := l.raw[1]
      let some ldecl := (← getLCtx).findFromUserName? target.getId | throwError m!"{target} not found"
      let some (𝓛, n, Γ, p) := ldecl.type.app4? ``Proof | throwError m!"{ldecl.type} is not a proof"
      let q ← mkFreshExprMVar (some (mkApp2 (.const ``Formula []) 𝓛 n))
      let goal := mkApp4 (.const ``Proof []) 𝓛 n Γ (mkApp4 (.const ``Formula.imp []) 𝓛 n p q)
          let (goalTerm, newGoals) ← papply (← elabTerm t none true) goal d
      let (_, mainGoal) ← (← getMainGoal).note ldecl.userName
        (mkApp7 (.const ``mp []) 𝓛 n Γ p q goalTerm ldecl.toExpr)
        (some (mkApp4 (.const ``Proof []) 𝓛 n Γ q))
      let mainGoal ← mainGoal.tryClear ldecl.fvarId
      replaceMainGoal (mainGoal :: newGoals)
    else if l.raw[1].getKind == numLitKind then
      let n := l.raw[1].toNat
      let [goal, newMainGoal] ← evalTacticAt
        (← `(tactic| (
          eapply cut
          on_goal 2 =>
            pswap 0 $(mkNatLit (n+1))
            pclear 0
          on_goal 1 =>
            eapply mp
            on_goal 2 => passumption $(mkNatLit n))))
        (← getMainGoal)
        | throwError "papply failed"
      let (goalTerm, newGoals) ← papply (← elabTerm t none true) (← goal.getType') d
      goal.assign goalTerm
      replaceMainGoal (newMainGoal :: newGoals)

/-- Apply the `n`-th assumption using `Proof.mp`. -/
syntax "papplya" num (location)? : tactic

macro_rules
| `(tactic| papplya $n) => do `(tactic| papply $(← hypTerm n.getNat))
| `(tactic| papplya $n at $l) => do `(tactic| papply $(← hypTerm n.getNat) at $l)

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

theorem imp_double_neg : Γ ⊢ p ⇒ ~ ~ p := by
  pintros
  papplya 0
  passumption

theorem double_neg_imp : Γ ⊢ ~ ~ p ⇒ p := by
  pintro
  papply transpose
  · exact imp_double_neg
  · passumption

theorem neg_imp_left : Γ ⊢ ~ (p ⇒ q) ⇒ p := by
  pintro
  papply double_neg_imp
  pintro
  papplya 1
  pintro
  papply false_elim
  papplya 1
  passumption

theorem neg_imp_right : Γ ⊢ ~ (p ⇒ q) ⇒ ~ q := by
  pintros
  papplya 1
  pintro
  passumption

theorem and_intro : Γ ⊢ p ⇒ q ⇒ p ⩑ q := by
  pintros
  papplya 0 <;> passumption

theorem and_left : Γ ⊢ p ⩑ q ⇒ p := by
  pintro
  papply double_neg_imp
  pintro
  papplya 1
  pintros
  papply false_elim
  papplya 2
  passumption

theorem and_right : Γ ⊢ p ⩑ q ⇒ q := by
  pintro
  papply double_neg_imp
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
  papply double_neg_imp
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

theorem or_elim' : Γ ⊢ (p ⇒ r) ⇒ (q ⇒ r) ⇒ p ⩒ q ⇒ r := by
  pintros; papply or_elim <;> passumption

theorem excluded_middle : Γ ⊢ ~ p ⩒ p := double_neg_imp

theorem andN_intro {v : Vec (𝓛.Formula n) m} :
  (∀ i, Γ ⊢ v i) → Γ ⊢ ⋀ i, v i := by
  intro h
  induction m with
  | zero => exact true_intro
  | succ n ih =>
    papply and_intro
    · apply h
    · apply ih; intro i; apply h

theorem andN_elim {v : Vec (𝓛.Formula n) m} (i : Fin m) :
  Γ ⊢ (⋀ i, v i) ⇒ v i := by
  induction m with
  | zero => exact i.elim0
  | succ n ih =>
    pintro
    cases i using Fin.cases with
    | zero => papply and_left at 0; passumption 0
    | succ i => papply and_right at 0; papply ih i at 0; passumption 0

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

theorem double_neg_iff : Γ ⊢ ~ ~ p ⇔ p := iff_intro.mp₂ double_neg_imp imp_double_neg

theorem neg_and_iff : Γ ⊢ ~ (p ⩑ q) ⇔ ~ p ⩒ ~ q := by
  papply iff_intro
  · pintros
    papplya 2
    papply and_intro
    · papply double_neg_imp
      passumption
    · passumption
  · papply or_elim' <;> pintros <;> papplya 1
      <;> [papply and_left; papply and_right] <;> passumption

theorem neg_or_iff : Γ ⊢ ~ (p ⩒ q) ⇔ ~ p ⩑ ~ q := by
  papply iff_intro
  · pintro
    papply and_intro <;> pintro <;> papplya 1
      <;> [papply or_inl; papply or_inr] <;> passumption
  · pintro
    papply or_elim'
    · papply and_left; passumption
    · papply and_right; passumption

theorem and_imp_iff : Γ ⊢ (p ⩑ q ⇒ r) ⇔ (p ⇒ q ⇒ r) := by
  papply iff_intro
  · pintros; papplya 2; papply and_intro <;> passumption
  · pintros; papplya 1 <;> [papply and_left; papply and_right] <;> passumption

theorem iff_congr_forall : Γ ⊢ ∀' (p ⇔ q) ⇒ ∀' p ⇔ ∀' q := by
  pintro
  papply iff_intro <;> papply forall_imp <;> prevert <;> papply forall_imp <;> apply forall_intro
  · exact iff_mp
  · exact iff_mpr

theorem neg_forall_iff : Γ ⊢ ~ ∀' p ⇔ ∃' (~ p) := iff_congr_neg.mp (iff_congr_forall.mp (forall_intro (iff_symm.mp double_neg_iff)))
theorem neg_exists_iff : Γ ⊢ ~ ∃' p ⇔ ∀' (~ p) := double_neg_iff
theorem neg_forall_neg_iff : Γ ⊢ ~ ∀' (~ p) ⇔ ∃' p := iff_refl
theorem neg_exists_neg_iff : Γ ⊢ ~ ∃' (~ p) ⇔ ∀' p := iff_trans.mp₂ double_neg_iff (iff_congr_forall.mp (forall_intro double_neg_iff))

theorem exists_intro (t) : Γ ⊢ p[↦ₛ t]ₚ ⇒ ∃' p := by
  pintros
  suffices _ ⊢ (~ p)[↦ₛ t]ₚ by
    papply this
    passumption
  papply forall_elim
  passumption

theorem exists_elim : Γ ⊢ ∃' p ⇒ (∀' (p ⇒ ↑ₚq)) ⇒ q := by
  pintros
  papply double_neg_imp
  pintros
  papplya 2
  papply forall_imp (p := p ⇒ ↑ₚq)
  · pintros; simp
    papplya 2
    papplya 1
    passumption
  · passumption

theorem exists_elim' : Γ ⊢ (∀' (p ⇒ ↑ₚq)) ⇒ ∃' p ⇒ q := by
  pintros; papply exists_elim <;> passumption

theorem exists_self : Γ ⊢ ∃' ↑ₚp ⇒ p := by
  pintro
  papply double_neg_imp
  pintro
  papplya 1
  papply forall_self (p := ~ p)
  passumption

theorem exists_imp : Γ ⊢ ∀' (p ⇒ q) ⇒ ∃' p ⇒ ∃' q := by
  pintro
  papply exists_elim'
  papply forall_imp (p := p ⇒ q)
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

theorem forallN_elim (σ) : Γ ⊢ ∀^[m] p ⇒ p[σ ++ᵥ Subst.id]ₚ := by
  rw [←Formula.subst_id (∀^[m] p)]
  apply forallN_elim'

theorem forallN_imp : Γ ⊢ ∀^[m] p ⇒ ∀^[m] (p ⇒ q) ⇒ ∀^[m] q := by
  pintros
  apply forallN_intro
  simp [Formula.shiftN_eq_subst]
  apply mp (p := p)
  · nth_rw 2 [←Formula.subst_id (p ⇒ q)]
    rw [Vec.eq_append Subst.id]
    papply forallN_elim'
    passumption
  · nth_rw 3 [←Formula.subst_id p]
    rw [Vec.eq_append Subst.id]
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
  `t₁ ≐ t` and `t ≐ t₂` (or `p ⇔ r` and `r ⇔ q`) using transtivity.
  
  A meta variable is generated for `t` or `r` if it is not given.
  -/
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
theorem RwFormula.matched : Γ ⊢ p ⇔ q → RwFormula Γ p q := id

@[prw] theorem RwTerm.refl : RwTerm Γ t t := by prefl
@[prw] theorem RwTermVec.refl : RwTermVec Γ v v := by intro; prefl
@[prw] theorem RwFormula.refl : RwFormula Γ p p := by prefl

@[prw] theorem RwTerm.func : RwTermVec Γ v₁ v₂ → RwTerm Γ (f ⬝ᶠ v₁) (f ⬝ᶠ v₂) := by
  intro h
  papply eq_congr_func
  exact andN_intro h

@[prw] theorem RwTermVec.cons : RwTerm Γ t₁ t₂ → RwTermVec Γ v₁ v₂ → RwTermVec Γ (t₁ ∷ᵥ v₁) (t₂ ∷ᵥ v₂) := by
  intro h₁ h₂ i
  exact i.cases h₁ h₂

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
 
@[prw] theorem RwFormula.neg : RwFormula Γ p q → RwFormula Γ (~ p) (~ q) := (imp · refl)

@[prw] theorem RwFormula.and : RwFormula Γ p₁ q₁ → RwFormula Γ p₂ q₂ → RwFormula Γ (p₁ ⩑ p₂) (q₁ ⩑ q₂) :=
  λ h₁ h₂ => neg (imp h₁ (neg h₂))

@[prw] theorem RwFormula.or : RwFormula Γ p₁ q₁ → RwFormula Γ p₂ q₂ → RwFormula Γ (p₁ ⩒ p₂) (q₁ ⩒ q₂) :=
  λ h₁ h₂ => imp (neg h₁) h₂

@[prw] theorem RwFormula.iff : RwFormula Γ p₁ q₁ → RwFormula Γ p₂ q₂ → RwFormula Γ (p₁ ⇔ p₂) (q₁ ⇔ q₂) :=
  λ h₁ h₂ => and (imp h₁ h₂) (imp h₂ h₁)

theorem RwFormula.symm : RwFormula Γ p q → RwFormula Γ q p := by
  intro h; psymm; exact h

theorem RwFormula.rewrite : RwFormula Γ p q → Γ ⊢ q → Γ ⊢ p := by
  intro h h₁
  papply iff_mpr
  · exact h
  · exact h₁

namespace Tactics

open Lean Parser Syntax Meta Elab Tactic

syntax prwRule := ("← "?) term

def prwRuleToTactic (rule : TSyntax ``prwRule) : MacroM (TSyntax ``tacticSeq) := do
  match rule with
  | `(prwRule | $n:num) => `(tacticSeq| pexact $(← hypTerm n.getNat))
  | `(prwRule | $t:term) => `(tacticSeq| pexact $t)
  | `(prwRule | ← $n:num) => `(tacticSeq| psymm; pexact $(← hypTerm n.getNat))
  | `(prwRule | ← $t:term) => `(tacticSeq| psymm; pexact $t)
  | _ => Macro.throwError "unknown syntax for prwRule {rule}"

def prwSolve (rule : TSyntax ``prwRule) (goal : MVarId) : TacticM (List MVarId) := do
  let tac ← liftMacroM (prwRuleToTactic rule)
  let prwThms := (prwExt.getState (← MonadEnv.getEnv)).reverse
  let mut newGoals := []
  let mut currentGoals := [goal]
  let mut success := false
  repeat
    let goal :: currentGoals' := currentGoals | break
    currentGoals := currentGoals'
    try
      let newGoals' ← evalTacticAt (←`(tactic|
        (first | apply RwTerm.matched | apply RwFormula.matched);
        with_reducible_and_instances $tac)) goal
      newGoals := newGoals ++ newGoals'
      success := true
    catch _ =>
      for thm in prwThms do
        try
          currentGoals := currentGoals ++ (←
            withReducibleAndInstances do
              evalTacticAt (←`(tactic| eapply $(mkIdent thm))) goal)
          break
        catch _ =>
          continue
  if !success then throwError m!"prw failed to rewrite {rule} on goal {goal}"
  return newGoals

/--
  `prw [e₁, ⋯, eₙ]` rewrites a proof goal `Γ ⊢ p` using given rules. A rule `e` can be either proof term or a
  number (the number of assumption), having type `Δ ⊢ t₁ ≐ t₂` or `Δ ⊢ q ⇔ r` (and `Δ` should be a subset of
  `Γ`). Also, `←e` reverse the direction of rewrite.
  
  - `prw [e₁, ⋯, eₙ]` will rewrite on the current goal.
  - `prw [e₁, ⋯, eₙ] at h` (where `h` is an identifier) will rewrite at local hypothesis `h`.
  - `prw [e₁, ⋯, eₙ] at n` (where `n` is a number) will rewrite on `n`-th assumption.
  -/
syntax "prw" "[" withoutPosition(prwRule,*,?) "]" (location)? : tactic

elab_rules : tactic
| `(tactic| prw [$rules,*]) => do
  for rule in rules.getElems do
    let rwGoal :: mainGoals ← evalTacticAt (← `(tactic| apply RwFormula.rewrite)) (← getMainGoal) | throwError "prw failed"
    let newGoals ← prwSolve rule rwGoal
    setGoals (mainGoals ++ newGoals)
    pruneSolvedGoals
| `(tactic| prw [$rules,*] at $h:ident) => do
    for rule in rules.getElems do
      let mainGoals ← evalTacticAt (← `(tactic| apply RwFormula.rewrite at $h)) (← getMainGoal)
      let some rwGoal := mainGoals.getLast? | throwError "prw failed"
      let mainGoals := mainGoals.dropLast
      let [rwGoal] ← evalTacticAt (← `(tactic| apply RwFormula.symm)) rwGoal | throwError "prw failed"
      let newGoals ← prwSolve rule rwGoal
      setGoals (mainGoals ++ newGoals)
      pruneSolvedGoals
| `(tactic| prw [$rules,*] at $n:num) => do
  for rule in rules.getElems do
    let [rwGoal, mainGoal] ← evalTacticAt (← `(tactic| eapply cut)) (← getMainGoal) | throwError "prw failed"
    let [rwGoal] ← evalTacticAt (← `(tactic| eapply RwFormula.rewrite; (on_goal 2 => passumption $n); eapply RwFormula.symm)) rwGoal | throwError "prw failed"
    let newGoals ← prwSolve rule rwGoal
    let mainGoal :: _ ← evalTacticAt (← `(tactic| (pswap 0 $(mkNatLit (n.getNat+1)); pclear 0))) mainGoal | throwError "prw failed"
    setGoals ([mainGoal] ++ newGoals)

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
    apply mp
    · apply weaken _ h₃; simp
    · apply weaken _ h₆; simp

end Proof

open Proof

namespace Theory

variable {𝓣 : 𝓛.Theory}

theorem generalization_alls : ↑ᵀ^[n] 𝓣 ⊢ p ↔ 𝓣 ⊢ ∀* p := by
  induction n with simp [Formula.alls]
  | succ n ih => rw [←shift_shiftN, generalization, ih]

theorem foralls_intro : ↑ᵀ^[n] 𝓣 ⊢ p → 𝓣 ⊢ ∀* p := generalization_alls.mp

theorem foralls_elim (σ : 𝓛.Subst n m) : 𝓣 ⊢ ∀* p → ↑ᵀ^[m] 𝓣 ⊢ p[σ]ₚ := by
  intro h
  induction n with simp [Formula.alls] at h
  | zero =>
    rw [Vec.eq_nil σ]; clear σ
    induction m with
    | zero => rw [←Vec.eq_nil Subst.id, Formula.subst_id]; exact h
    | succ m ih =>
      apply shift at ih
      simp [Formula.shift, ←Formula.subst_comp, Vec.eq_nil] at ih
      exact ih
  | succ n ih =>
    apply ih (σ := σ.tail) at h
    simp at h
    apply (forall_elim σ.head).mp at h
    rw [←Formula.subst_comp, Subst.lift_comp_single, ←Vec.eq_cons] at h
    exact h

theorem foralls_imp : 𝓣 ⊢ ∀* (p ⇒ q) ⇒ ∀* p ⇒ ∀* q := by
  pintros
  apply foralls_intro
  apply mp (p := p) <;> rw [generalization_alls] <;> passumption

theorem iff_congr_foralls : 𝓣 ⊢ ∀* (p ⇔ q) ⇒ ∀* p ⇔ ∀* q := by
  pintro
  papply iff_intro <;> papply foralls_imp <;> papply foralls_intro
  · papply iff_mp; rw [generalization_alls]; passumption
  · papply iff_mpr; rw [generalization_alls]; passumption

abbrev theorems (𝓣 : 𝓛.Theory) : 𝓛.Theory := { p | 𝓣 ⊢ p }

abbrev Decidable (𝓣 : 𝓛.Theory) := DecidablePred 𝓣.theorems

end Theory

notation Γ:50 "⊬" p:50 => ¬ Γ ⊢ p

def Consistent (Γ : 𝓛.FormulaSet n) := Γ ⊬ ⊥

theorem Consistent.weaken : Γ ⊆ Δ → Consistent Δ → Consistent Γ := by
  intros h₁ h₂ h
  apply h₂
  exact h.weaken h₁

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
    papply imp_double_neg
    exact h₂
  · intro h₁ h₂
    apply h₁
    papply double_neg_imp
    pintro
    exact h₂

theorem Consistent.undisprovable : Consistent Γ → Γ ⊢ p → Γ ⊬ ~ p := by
  intro h h₁ h₂
  apply h
  papply h₂
  exact h₁

theorem Consistent.unprovable : Consistent Γ → Γ ⊢ ~ p → Γ ⊬ p := by
  intro h h₁ h₂
  apply h
  papply h₁
  exact h₂

def Complete (Γ : 𝓛.FormulaSet n) := ∀ p, Γ ⊢ p ∨ Γ ⊢ ~ p

theorem Complete.neg_provable_of_unprovable (h : Complete Γ) : Γ ⊬ p → Γ ⊢ ~ p := by
  rcases h p with h₁ | h₁ <;> simp [h₁]

theorem Complete.unprovable_iff (h₁ : Complete Γ) (h₂ : Consistent Γ) : Γ ⊬ p ↔ Γ ⊢ ~ p := by
  rcases h₁ p with h | h <;> simp [h] <;> intro h'
  · exact h₂ (h'.mp h)
  · exact h₂ (h.mp h')

def Henkin (Γ : 𝓛.FormulaSet n) := ∀ p, Γ ⊢ ∃' p → ∃ (c : 𝓛.Const), Γ ⊢ p[↦ₛ c]ₚ

end FirstOrder.Language
