import Mathlib.Data.Set.Finite.Basic
import MathematicalLogic.FirstOrder.Syntax
import MathematicalLogic.FirstOrder.Proof.Init

namespace FirstOrder.Language

/--
  First-order axioms. Note that these are logical axioms -- theory related axioms (e.g. arithmetic)
  should occur as hypotheses.
  
  The axioms in our proof system include:
  1. 3 axioms for propositional logic, `imp_imp_self`, `imp_distrib` and `imp_contra`;
  2. 3 axioms for quantifiers, `forall_elim`, `forall_self` and `forall_imp`;
  3. 5 axioms for equality, `eq_refl`, `eq_symm`, `eq_trans`, `eq_congr_func` and `eq_congr_rel`;
  4. the universal closure of all axioms generated by 1-3.
  -/
inductive Axiom (L : Language) : L.FormulaSet n where
| imp_imp_self : L.Axiom (p ⇒ q ⇒ p)
| imp_distrib : L.Axiom ((p ⇒ q ⇒ r) ⇒ (p ⇒ q) ⇒ p ⇒ r)
| imp_contra : L.Axiom ((~ p ⇒ ~ q) ⇒ q ⇒ p)
| forall_elim : L.Axiom (∀' p ⇒ p[↦ₛ t]ₚ)
| forall_self : L.Axiom (p ⇒ ∀' ↑ₚp)
| forall_imp : L.Axiom (∀' (p ⇒ q) ⇒ ∀' p ⇒ ∀' q)
| eq_refl : L.Axiom (t ≐ t)
| eq_symm : L.Axiom (t₁ ≐ t₂ ⇒ t₂ ≐ t₁)
| eq_trans : L.Axiom (t₁ ≐ t₂ ⇒ t₂ ≐ t₃ ⇒ t₁ ≐ t₃)
| eq_congr_func : L.Axiom ((⋀ i, v₁ i ≐ v₂ i) ⇒ f ⬝ᶠ v₁ ≐ f ⬝ᶠ v₂)
| eq_congr_rel : L.Axiom ((⋀ i, v₁ i ≐ v₂ i) ⇒ r ⬝ʳ v₁ ⇒ r ⬝ʳ v₂)
| all : L.Axiom p → L.Axiom (∀' p)

variable {L : Language}

theorem Axiom.subst {σ : L.Subst n m} : p ∈ L.Axiom → p[σ]ₚ ∈ L.Axiom := by
  intro h
  induction h generalizing m <;> simp [Term.shift_subst_lift, Formula.shift_subst_lift, Formula.subst_swap_single, Formula.subst_andN]
  case all ih => exact all ih
  all_goals constructor

/-- Hilbert-style proof. -/
inductive Proof (Γ : L.FormulaSet n) : L.Formula n → Prop where
| hyp : p ∈ Γ → Proof Γ p
| ax : p ∈ L.Axiom → Proof Γ p
| mp : Proof Γ (p ⇒ q) → Proof Γ p → Proof Γ q
infix:50 " ⊢ " => Proof

/--
  Theory `T₁` is a subtheory of `T₂` (`T₁ ⊆ᵀ T₂`) if `T₂` can proves all formulas in `T₁`. When that
  is true, all theorems of `T₁` are also theorems of `T₂` (see `Proof.cut`).
  
  This is designed as a typeclass so that, if there is an instance of `T₁ ⊆ᵀ T₂`, all theorems proved
  for `T₁` can be applied to `T₂` automatically when using `papply` tactic.
  
  Note: we define `Subtheory` for `FormulaSet n` in general, but the instances should always be for
  `Theory`.
  -/
class Subtheory (Γ Δ : L.FormulaSet n) : Prop where
  subtheory : ∀ p ∈ Γ, Δ ⊢ p
infix:50 " ⊆ᵀ " => Subtheory

theorem Subtheory.of_subset : Γ ⊆ Δ → Γ ⊆ᵀ Δ :=
  λ h => ⟨λ _ h' => .hyp (h h')⟩

namespace Proof

theorem hyp_append : Γ,' p ⊢ p := hyp FormulaSet.mem_append

theorem cut : Γ ⊆ᵀ Δ → Γ ⊢ p → Δ ⊢ p := by
  intro h₁ h₂
  induction h₂ with
  | hyp h => exact h₁.subtheory _ h
  | ax h => exact ax h
  | mp _ _ ih₁ ih₂ => exact mp ih₁ ih₂

theorem weaken : Γ ⊆ Δ → Γ ⊢ p → Δ ⊢ p := λ h => cut (.of_subset h)

theorem weaken_append : Γ ⊢ p → Γ,' q ⊢ p := weaken FormulaSet.subset_append

theorem mp₂ (h₁ : Γ ⊢ p ⇒ q ⇒ r) (h₂ : Γ ⊢ p) (h₃ : Γ ⊢ q) : Γ ⊢ r := mp (mp h₁ h₂) h₃

theorem identity : Γ ⊢ p ⇒ p :=
  mp₂ (ax .imp_distrib) (ax .imp_imp_self) (ax (.imp_imp_self (q := p)))

/-- Deduction theorem. -/
theorem deduction : Γ ⊢ p ⇒ q ↔ Γ,' p ⊢ q := by
  constructor
  · intro h; exact mp (weaken_append h) hyp_append
  · intro h
    induction h with
    | hyp h =>
      cases h with
      | inl h => subst h; exact identity
      | inr h => exact mp (ax .imp_imp_self) (hyp h)
    | ax h => exact mp (ax .imp_imp_self) (ax h)
    | mp _ _ ih₁ ih₂ => exact mp (mp (ax .imp_distrib) ih₁) ih₂

theorem cut_append (h₁ : Γ ⊢ p) (h₂ : Γ,' p ⊢ q) : Γ ⊢ q := mp (deduction.mpr h₂) h₁

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

/-- Generalization theorem. -/
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

end Proof

namespace Subtheory

instance refl : Γ ⊆ᵀ Γ where
  subtheory _ h := .hyp h

theorem trans (h₁ : Γ₁ ⊆ᵀ Γ₂) (h₂ : Γ₂ ⊆ᵀ Γ₃) : Γ₁ ⊆ᵀ Γ₃ where
  subtheory _ h := .cut h₂ (h₁.subtheory _ h)

theorem append (h : Γ ⊆ᵀ Δ) : Γ ⊆ᵀ Δ,' p := h.trans (of_subset FormulaSet.subset_append)

theorem append_append (h : Γ ⊆ᵀ Δ) : Γ,' p ⊆ᵀ Δ,' p where
  subtheory
  | _, .inl rfl => .hyp_append
  | _, .inr h' => .weaken_append (h.subtheory _ h')

theorem shift (h : Γ ⊆ᵀ Δ) : ↑ᴳΓ ⊆ᵀ ↑ᴳΔ where
  subtheory _ h' := by
    simp [FormulaSet.shift] at h'
    rcases h' with ⟨p, h', rfl⟩
    exact .shift (h.subtheory p h')

theorem shiftN (h : Γ ⊆ᵀ Δ) : ↑ᴳ^[m] Γ ⊆ᵀ ↑ᴳ^[m] Δ := by
  induction m with
  | zero => exact h
  | succ m ih => exact shift ih

theorem shiftT {T₁ T₂ : L.Theory} (h : T₁ ⊆ᵀ T₂) : ↑ᵀ^[n] T₁ ⊆ᵀ ↑ᵀ^[n] T₂ := by
  induction n with
  | zero => exact h
  | succ n ih => exact shift ih

end Subtheory

namespace Proof.Tactic

open Lean Syntax Meta Elab Tactic

/-- Introduce a new hypothesis or a new variable. -/
macro "pintro" : tactic => `(tactic|
  first
  | eapply deduction.mpr
  | (eapply forall_intro;
     try simp only [FormulaSet.shift_append, FormulaSet.shiftN_append,
       Theory.shift_eq, Theory.shift_shiftN, Theory.shiftN_eq, Theory.shiftN_shiftN]))

/-- Revert a hypothesis through deduction theorem. -/
macro "prevert" : tactic => `(tactic| eapply deduction.mp)

/-- Repeatedly introduce new hypotheses and variables. Use `pintros n` to control the number of hypothesis introduced. -/
macro "pintros" n:(ppSpace colGt num)? : tactic =>
  match n with
  | some n => `(tactic| iterate $n pintro)
  | none => `(tactic| repeat pintro)

def hypTerm (n : ℕ) : MacroM (TSyntax `term) := do
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
  `(tactic| refine cut_append (p := $t) ?_ ?_)

/-- For goal `Γ ⊢ p`, `psuffices q` proves `Γ, q ⊢ p` first and then proves `Γ ⊢ q`. -/
macro "psuffices" t:(ppSpace colGt term) : tactic =>
  `(tactic| (refine cut_append (p := $t) ?_ ?_; swap))

/-- Remove the `n`-th assumption. -/
elab "pclear" n:(ppSpace colGt num) : tactic => do
  let mut weakenTerm ← `(FormulaSet.subset_append)
  for _ in [:n.getNat] do
    weakenTerm ← `(FormulaSet.append_subset_append $weakenTerm)
  let mainGoal :: _ ← evalTacticAt (← `(tactic| eapply weaken $weakenTerm)) (← getMainGoal) | throwError "pclear failed"
  replaceMainGoal [mainGoal]

/-- Remove all assumptions except the `FormulaSet`. -/
macro "pclears" : tactic => `(tactic| repeat pclear 0)

/-- Swap the `n`-th assumption and the `m`-th assumption. -/
elab "pswap" n:(ppSpace colGt num) m:(ppSpace colGt num) : tactic => do
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

/-- Replaces the `n`-th assumption with a new proposition, and generate a new goal to prove `Γ, ⋯ ⊢ p`. -/
macro "preplace" n:(ppSpace colGt num) t:(ppSpace colGt term) : tactic =>
  `(tactic| (psuffices $t; focus (pswap 0 $(mkNatLit (n.getNat+1)); pclear 0)))

def isTheory? (n : Expr) (Γ : Expr) : Option Expr :=
  if n.isConstOf `Nat.zero then Γ
  else if let some (_, _, T) := Γ.app3? ``Theory.shiftT then T
  else none

partial def formulaList (Γ : Expr) : Expr × List Expr :=
  if let some (_, _, Γ', p) := Γ.app4? ``FormulaSet.append then
    let (Δ, l) := formulaList Γ'
    (Δ, l ++ [p])
  else
    (Γ, [])

/-- Unify `Γ` as a subtheory of `Δ`; if succeed, return a term of type `Γ ⊆ᵀ Δ`. -/
partial def isSubtheoryOf (L n Γ Δ : Expr) : MetaM (Option Expr) := do
  let mut (Γ, l₁) := formulaList Γ
  let mut (Δ, l₂) := formulaList Δ
  if l₁.length > l₂.length then failure
  let mut weakenTerm := mkApp3 (.const ``Subtheory.refl []) L n Γ
  if Γ.isMVar then
    -- if Γ is a mvar, we try to unify `Γ` as large as possible
    let (l₂', l₂'') := l₂.splitAt (l₂.length - l₁.length)
    for q in l₂' do
      Δ := mkApp4 (.const ``FormulaSet.append []) L n Δ q
    Γ.mvarId!.assign Δ
    l₂ := l₂''
  else if let (some T₁, some T₂) := (isTheory? n Γ, isTheory? n Δ) then
    weakenTerm := mkApp5 (.const ``Subtheory.shiftT []) L n T₁ T₂
      (← synthInstance (mkApp4 (.const ``Subtheory []) L (.const `Nat.zero []) T₁ T₂))
  else
    let true := ← isDefEq Γ Δ | failure
  for (p, q) in l₁.zipRight l₂ do
    match p with
    | some p =>
      let .true := ← isDefEq p q | failure
      weakenTerm := mkApp6 (.const ``Subtheory.append_append []) L n Γ Δ p weakenTerm
      Γ := mkApp4 (.const ``FormulaSet.append []) L n Γ p
      Δ := mkApp4 (.const ``FormulaSet.append []) L n Δ p
    | none =>
      weakenTerm := mkApp6 (.const ``Subtheory.append []) L n Γ Δ q weakenTerm
      Δ := mkApp4 (.const ``FormulaSet.append []) L n Δ q
  return some weakenTerm

/--
  `f` should be a term of type `Γ ⊢ p₁ ⇒ p₂ ⇒ ⋯ ⇒ pₙ ⇒ q`, and `goal` should be a type `Δ ⊢ pₙ` (in
  whnf) where `Γ ⊆ᵀ Δ`.
  
  `apply f goal d` will create a term `Proof.mp (Proof.mp (... (Proof.mp f ?m₁)) ?mₙ₋₁) ?mₙ` of
  type `goal`, return the term and a list of `?m₁, ⋯, ?mₙ`.
  -/
private def papply (f : Expr) (goal : Expr) (d : Option ℕ) : TacticM (Expr × List MVarId) := do
  let (fmvars, _, ftype) ← forallMetaTelescopeReducing (← instantiateMVars (← inferType f))
  let some (L, n, Γ, p) := ftype.app4? ``Proof | throwError m!"{ftype} is not a proof"
  let some (L', n', Δ, _) := goal.app4? ``Proof | throwError m!"{goal} is not a proof"
  let true := ← isDefEq L L' | throwError m!"failed to unify {L} and {L'}"
  let true := ← isDefEq n n' | throwError m!"failed to unify {n} and {n'}"
  let some weakenTerm ← isSubtheoryOf L n Γ Δ | throwError m!"{Γ} is not a subtheory of {Δ}"
  let mut proofTerm := mkApp7 (.const ``cut []) L n Γ Δ p weakenTerm (mkAppN f fmvars)
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
      let mvar ← mkFreshExprMVarWithId mvarId (some (mkApp4 (.const ``Proof []) L n Δ p))
      proofTerm := mkApp7 (.const ``mp []) L n Δ p q proofTerm mvar
      goalFormula := q
    else
      throwError "failed to apply {ftype} at {goal}"
  for mvar in fmvars do
    if !(← mvar.mvarId!.isAssigned) then
      newMVarIds := newMVarIds ++ [mvar.mvarId!]
  return (proofTerm, newMVarIds)

def runPapplyAtMainGoal (f : TSyntax `term) (depth : Option ℕ) : TacticM Unit := withMainContext do
  let mainGoal ← getMainGoal
  let (goalTerm, newGoals) ← papply (← elabTerm f none true) (← mainGoal.getType') depth
  mainGoal.assign goalTerm
  replaceMainGoal newGoals

def runPapplyAtLocalHyp (f : TSyntax `term) (target : TSyntax `ident) (depth : Option ℕ) : TacticM Unit := withMainContext do
  let some ldecl := (← getLCtx).findFromUserName? target.getId | throwError m!"{target} not found"
  let some (L, n, Γ, p) := ldecl.type.app4? ``Proof | throwError m!"{ldecl.type} is not a proof"
  let q ← mkFreshExprMVar (some (mkApp2 (.const ``Formula []) L n))
  let goal := mkApp4 (.const ``Proof []) L n Γ (mkApp4 (.const ``Formula.imp []) L n p q)
  let (goalTerm, newGoals) ← papply (← elabTerm f none true) goal depth
  let (_, mainGoal) ← (← getMainGoal).note ldecl.userName
    (mkApp7 (.const ``mp []) L n Γ p q goalTerm ldecl.toExpr)
    (some (mkApp4 (.const ``Proof []) L n Γ q))
  let mainGoal ← mainGoal.tryClear ldecl.fvarId
  replaceMainGoal (mainGoal :: newGoals)

def runPapplyAtAssumption (f : TSyntax `term) (target : ℕ) (depth : Option ℕ) : TacticM Unit := withMainContext do
  let [goal, newMainGoal] ← evalTacticAt
    (← `(tactic| (
      eapply cut_append
      on_goal 2 =>
        pswap 0 $(mkNatLit (target+1))
        pclear 0
      on_goal 1 =>
        eapply mp
        on_goal 2 => passumption $(mkNatLit target))))
    (← getMainGoal)
    | throwError "papply failed"
  let (goalTerm, newGoals) ← papply (← elabTerm f none true) (← goal.getType') depth
  goal.assign goalTerm
  replaceMainGoal (newMainGoal :: newGoals)

syntax location := "at" (ident <|> num)

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
syntax "papply" ppSpace colGt term (location)? ("with" num)? : tactic

elab_rules : tactic
| `(tactic| papply $t) => runPapplyAtMainGoal t none
| `(tactic| papply $t with $d) => runPapplyAtMainGoal t (some d.getNat)
| `(tactic| papply $t at $h:ident) => runPapplyAtLocalHyp t h none
| `(tactic| papply $t at $h:ident with $d) => runPapplyAtLocalHyp t h (some d.getNat)
| `(tactic| papply $t at $n:num) => runPapplyAtAssumption t n.getNat none
| `(tactic| papply $t at $n:num with $d) => runPapplyAtAssumption t n.getNat (some d.getNat)

/-- Apply the `n`-th assumption using `Proof.mp`. -/
syntax "papplya" (ppSpace colGt num) (location)? : tactic

macro_rules
| `(tactic| papplya $n) => do `(tactic| papply $(← hypTerm n.getNat))
| `(tactic| papplya $n at $l) => do `(tactic| papply $(← hypTerm n.getNat) at $l)

/-- Close the goal with given proof term. -/
macro "pexact" t:(ppSpace colGt term) : tactic => `(tactic| papply $t with 0)

end Tactic

theorem composition : Γ ⊢ (p ⇒ q) ⇒ (q ⇒ r) ⇒ p ⇒ r := by
  pintros
  papplya 1
  papplya 2
  passumption

theorem imp_contra : Γ ⊢ (~ p ⇒ ~ q) ⇒ q ⇒ p := ax .imp_contra

theorem true_intro : Γ ⊢ ⊤ := identity

theorem false_elim : Γ ⊢ ⊥ ⇒ p := by
  papply imp_contra
  pintro
  exact true_intro

theorem imp_double_neg : Γ ⊢ p ⇒ ~ ~ p := by
  pintros
  papplya 0
  passumption

theorem double_neg_imp : Γ ⊢ ~ ~ p ⇒ p := by
  papply imp_contra
  pexact imp_double_neg

namespace Tactic

/-- Proof by contradiction. -/
macro "pcontra" : tactic => `(tactic| (papply double_neg_imp; pintro))

end Tactic

theorem and_intro : Γ ⊢ p ⇒ q ⇒ p ⩑ q := by
  pintros
  papplya 0 <;> passumption

theorem and_left : Γ ⊢ p ⩑ q ⇒ p := by
  pintro
  pcontra
  papplya 1
  pintros
  papply false_elim
  papplya 2
  passumption

theorem and_right : Γ ⊢ p ⩑ q ⇒ q := by
  pintro
  pcontra
  papplya 1
  pintro
  passumption

theorem or_inl : Γ ⊢ p ⇒ p ⩒ q := by
  pintros
  papply false_elim
  papplya 0
  passumption

theorem or_inr : Γ ⊢ q ⇒ p ⩒ q := ax .imp_imp_self

theorem or_elim : Γ ⊢ p ⩒ q ⇒ (p ⇒ r) ⇒ (q ⇒ r) ⇒ r := by
  pintros
  pcontra
  papplya 0
  papplya 2
  pcontra
  papplya 1
  papplya 2
  papplya 4
  passumption

theorem or_elim' : Γ ⊢ (p ⇒ r) ⇒ (q ⇒ r) ⇒ p ⩒ q ⇒ r := by
  pintros; papply or_elim <;> passumption

theorem excluded_middle : Γ ⊢ ~ p ⩒ p := double_neg_imp

theorem andN_intro {v : Vec (L.Formula n) m} :
  (∀ i, Γ ⊢ v i) → Γ ⊢ ⋀ i, v i := by
  intro h
  induction m with
  | zero => exact true_intro
  | succ n ih =>
    papply and_intro
    · apply h
    · apply ih; intro i; apply h

theorem andN_elim {v : Vec (L.Formula n) m} (i : Fin m) :
  Γ ⊢ (⋀ i, v i) ⇒ v i := by
  induction m with
  | zero => exact i.elim0
  | succ n ih =>
    pintro
    cases i using Fin.cases with
    | zero => papply and_left at 0; passumption 0
    | succ i => papply and_right at 0; papply ih i at 0; passumption 0

theorem orN_intro {v : Vec (L.Formula n) m} (i : Fin m) :
  Γ ⊢ v i ⇒ ⋁ i, v i := by
  induction m with
  | zero => exact i.elim0
  | succ n ih =>
    pintro
    cases i using Fin.cases with
    | zero => papply or_inl; passumption 0
    | succ i => papply or_inr; papply ih; passumption 0

theorem orN_elim' {v : Vec (L.Formula n) m} :
  (∀ i, Γ ⊢ v i ⇒ p) → Γ ⊢ (⋁ i, v i) ⇒ p := by
  intro h
  induction m generalizing Γ with
  | zero =>
    pexact false_elim
  | succ m ih =>
    papply or_elim'
    · pexact h 0
    · papply ih
      intro i
      exact h i.succ

theorem orN_elim {v : Vec (L.Formula n) m} :
  Γ ⊢ ⋁ i, v i → (∀ i, Γ ⊢ v i ⇒ p) → Γ ⊢ p := by
  intro h₁ h₂
  papply orN_elim' h₂
  exact h₁

theorem iff_intro : Γ ⊢ (p ⇒ q) ⇒ (q ⇒ p) ⇒ (p ⇔ q) := and_intro
theorem iff_mp : Γ ⊢ (p ⇔ q) ⇒ (p ⇒ q) := and_left
theorem iff_mpr : Γ ⊢ (p ⇔ q) ⇒ (q ⇒ p) := and_right
theorem iff_iff : Γ ⊢ p ⇔ q → (Γ ⊢ p ↔ Γ ⊢ q) := λ h => ⟨iff_mp.mp₂ h, iff_mpr.mp₂ h⟩

@[prw] theorem iff_refl : Γ ⊢ p ⇔ p := mp₂ iff_intro identity identity

theorem iff_symm : Γ ⊢ (p ⇔ q) ⇒ (q ⇔ p) := by
  pintro
  papply iff_intro
  · papply iff_mpr; passumption
  · papply iff_mp; passumption

theorem iff_comm : Γ ⊢ (p ⇔ q) ⇔ (q ⇔ p) := by
  papply iff_intro <;> pexact iff_symm

theorem iff_trans : Γ ⊢ (p ⇔ q) ⇒ (q ⇔ r) ⇒ (p ⇔ r) := by
  pintros 2
  papply iff_intro
  · papply composition <;> papply iff_mp <;> passumption
  · papply composition <;> papply iff_mpr <;> passumption

@[prw] theorem iff_congr_imp : Γ ⊢ (p₁ ⇔ p₂) ⇒ (q₁ ⇔ q₂) ⇒ ((p₁ ⇒ q₁) ⇔ (p₂ ⇒ q₂)) := by
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

@[prw] theorem iff_congr_neg : Γ ⊢ (p ⇔ q) ⇒ (~ p ⇔ ~ q) := by
  pintro
  papply iff_congr_imp
  · passumption
  · exact iff_refl

@[prw] theorem iff_congr_and : Γ ⊢ (p₁ ⇔ p₂) ⇒ (q₁ ⇔ q₂) ⇒ (p₁ ⩑ q₁ ⇔ p₂ ⩑ q₂) := by
  pintros 2
  papply iff_congr_neg
  papply iff_congr_imp
  · passumption
  · papply iff_congr_neg
    passumption

@[prw] theorem iff_congr_or : Γ ⊢ (p₁ ⇔ p₂) ⇒ (q₁ ⇔ q₂) ⇒ (p₁ ⩒ q₁ ⇔ p₂ ⩒ q₂) := by
  pintros 2
  papply iff_congr_imp
  · papply iff_congr_neg
    passumption
  · passumption

@[prw] theorem iff_congr_iff : Γ ⊢ (p₁ ⇔ p₂) ⇒ (q₁ ⇔ q₂) ⇒ ((p₁ ⇔ q₁) ⇔ (p₂ ⇔ q₂)) := by
  pintros 2
  papply iff_congr_and <;> papply iff_congr_imp <;> passumption

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

theorem neg_or_iff_imp : Γ ⊢ ~ p ⩒ q ⇔ (p ⇒ q) := by
  papply iff_intro
  · papply or_elim'
    · pintros; papply false_elim; papplya 1; passumption
    · pintros; passumption
  · pintros
    papplya 1
    papply double_neg_imp
    passumption

theorem neg_imp_iff : Γ ⊢ ~ (p ⇒ q) ⇔ p ⩑ ~ q := by
  papply iff_intro
  · pintros
    papplya 1
    pintro
    papply double_neg_imp
    papplya 1
    passumption
  · pintros
    phave ~ q
    · papply and_right; passumption
    · papplya 0; papplya 1; papply and_left; passumption

theorem and_imp_iff : Γ ⊢ (p ⩑ q ⇒ r) ⇔ (p ⇒ q ⇒ r) := by
  papply iff_intro
  · pintros; papplya 2; papply and_intro <;> passumption
  · pintros; papplya 1 <;> [papply and_left; papply and_right] <;> passumption

theorem and_comm : Γ ⊢ p ⩑ q ⇔ q ⩑ p := by
  papply iff_intro <;> pintro <;> papply and_intro
    <;> first | papply and_right; passumption 0 | papply and_left; passumption 0

theorem and_assoc : Γ ⊢ (p ⩑ q) ⩑ r ⇔ p ⩑ q ⩑ r := by
  papply iff_intro <;> pintro <;> papply and_intro <;> (try papply and_intro)
   <;> aesop (add unsafe tactic (by papply and_left), unsafe tactic (by papply and_right), safe tactic (by passumption 0))

theorem or_comm : Γ ⊢ p ⩒ q ⇔ q ⩒ p := by
  papply iff_intro <;> papply or_elim' <;> first | pexact or_inl | pexact or_inr

theorem or_assoc : Γ ⊢ (p ⩒ q) ⩒ r ⇔ p ⩒ q ⩒ r := by
  papply iff_intro <;> papply or_elim' <;> (try papply or_elim' with 2) <;> pintro
   <;> aesop (add unsafe tactic (by papply or_inl), unsafe tactic (by papply or_inr), safe tactic (by passumption 0))

theorem iff_congr_forall : Γ ⊢ ∀' (p ⇔ q) ⇒ ∀' p ⇔ ∀' q := by
  pintro
  papply iff_intro <;> papply forall_imp <;> prevert <;> papply forall_imp <;> apply forall_intro
  · exact iff_mp
  · exact iff_mpr

theorem neg_forall_iff : Γ ⊢ ~ ∀' p ⇔ ∃' (~ p) :=
  iff_congr_neg.mp (iff_congr_forall.mp (forall_intro (iff_symm.mp double_neg_iff)))

theorem neg_exists_iff : Γ ⊢ ~ ∃' p ⇔ ∀' (~ p) := double_neg_iff

theorem neg_forall_neg_iff : Γ ⊢ ~ ∀' (~ p) ⇔ ∃' p := iff_refl

theorem neg_exists_neg_iff : Γ ⊢ ~ ∃' (~ p) ⇔ ∀' p :=
  iff_trans.mp₂ double_neg_iff (iff_congr_forall.mp (forall_intro double_neg_iff))

theorem exists_intro (t) : Γ ⊢ p[↦ₛ t]ₚ ⇒ ∃' p := by
  pintros
  suffices _ ⊢ (~ p)[↦ₛ t]ₚ by
    papply this
    passumption
  papply forall_elim
  passumption

theorem exists_elim : Γ ⊢ ∃' p ⇒ (∀' (p ⇒ ↑ₚq)) ⇒ q := by
  pintros
  pcontra
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
  pcontra
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

theorem existsN_intro' {p : L.Formula (k + m)} (σ₁) : Γ ⊢ p[σ₁ ++ᵥ σ₂]ₚ ⇒ (∃^[m] p)[σ₂]ₚ := by
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

theorem existsN_intro {p : L.Formula (n + m)} (σ) :
  Γ ⊢ p[σ ++ᵥ Subst.id]ₚ ⇒ ∃^[m] p := by
  rw [←Formula.subst_id (∃^[m] p)]
  apply existsN_intro'

theorem existsN_elim {p : L.Formula (n + m)} :
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

theorem existsN_elim' : Γ ⊢ ∀^[m] (p ⇒ ↑ₚ^[m] q) ⇒ ∃^[m] p ⇒ q := by
  pintros; papply existsN_elim <;> passumption

@[prw] theorem eq_refl : Γ ⊢ t ≐ t := ax .eq_refl

theorem eq_symm : Γ ⊢ t₁ ≐ t₂ ⇒ t₂ ≐ t₁ := ax .eq_symm

theorem eq_trans : Γ ⊢ t₁ ≐ t₂ ⇒ t₂ ≐ t₃ ⇒ t₁ ≐ t₃ := ax .eq_trans

theorem eq_comm (t₁ t₂) : Γ ⊢ t₁ ≐ t₂ ⇔ t₂ ≐ t₁ := by
  papply iff_intro <;> pexact eq_symm

namespace Tactic

/-- Close the proof goal `t ≐ t` or `p ⇔ p` using reflexivity. -/
macro "prefl" : tactic => `(tactic| first | pexact eq_refl | pexact iff_refl)

/-- If the proof goal is `t₁ ≐ t₂` or `p ⇔ q`, replace it with `t₂ ≐ t₁` or `q ⇔ p` using symmetry. -/
macro "psymm" : tactic => `(tactic| first | papply eq_symm | papply iff_symm)

/--
  If the proof goal is `t₁ ≐ t₂` (or `p ⇔ q`), replace it with two goals,
  `t₁ ≐ t` and `t ≐ t₂` (or `p ⇔ r` and `r ⇔ q`) using transitivity.
  
  A meta variable is generated for `t` or `r` if it is not given.
  -/
macro "ptrans" t:(ppSpace colGt term)? : tactic =>
  match t with
  | some t => `(tactic| first | papply eq_trans (t₂ := $t) | papply iff_trans (q := $t))
  | none => `(tactic| first | papply eq_trans | papply iff_trans)

end Tactic

theorem eq_congr_func : Γ ⊢ (⋀ i, v₁ i ≐ v₂ i) ⇒ f ⬝ᶠ v₁ ≐ f ⬝ᶠ v₂ := ax .eq_congr_func

theorem eq_congr_subst (h : ∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) : Γ ⊢ t[σ₁]ₜ ≐ t[σ₂]ₜ := by
  induction t with simp
  | var => apply h
  | func f v ih => papply eq_congr_func; apply andN_intro; exact ih

theorem eq_congr_subst_single : Γ ⊢ t₁ ≐ t₂ ⇒ t[↦ₛ t₁]ₜ ≐ t[↦ₛ t₂]ₜ := by
  pintro
  apply eq_congr_subst
  intro i
  cases i using Fin.cases with simp
  | zero => passumption
  | succ i => prefl

theorem eq_congr_eq : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ ≐ t₂ ⇒ t₁' ≐ t₂' := by
  pintros
  ptrans
  · psymm; passumption
  · ptrans <;> passumption

@[prw] theorem iff_congr_eq : Γ ⊢ t₁ ≐ t₁' ⇒ t₂ ≐ t₂' ⇒ t₁ ≐ t₂ ⇔ t₁' ≐ t₂' := by
  pintros 2
  papply iff_intro
  · papply eq_congr_eq <;> passumption
  · papply eq_congr_eq <;> psymm <;> passumption

theorem eq_congr_rel : Γ ⊢ (⋀ i, v₁ i ≐ v₂ i) ⇒ r ⬝ʳ v₁ ⇒ r ⬝ʳ v₂ := ax .eq_congr_rel

theorem iff_congr_rel : Γ ⊢ (⋀ i, v₁ i ≐ v₂ i) ⇒ r ⬝ʳ v₁ ⇔ r ⬝ʳ v₂ := by
  pintro
  papply iff_intro <;> papply eq_congr_rel
  · passumption
  · apply andN_intro
    intro i
    psymm
    papply andN_elim (v := λ i => v₁ i ≐ v₂ i)
    passumption

theorem iff_congr_subst {Γ : L.FormulaSet n} (h : ∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) : Γ ⊢ p[σ₁]ₚ ⇔ p[σ₂]ₚ := by
  induction p generalizing n with simp
  | rel r v =>
    papply iff_congr_rel; apply andN_intro; intro; apply eq_congr_subst; exact h
  | eq t₁ t₂ =>
    papply iff_congr_eq <;> apply eq_congr_subst <;> exact h
  | false =>
    exact iff_refl
  | imp p q ih₁ ih₂ =>
    papply iff_congr_imp <;> apply_assumption <;> exact h
  | all p ih =>
    papply iff_congr_forall; apply forall_intro; apply ih; intro i
    cases i using Fin.cases with simp
    | zero => prefl
    | succ i => apply shift (p := σ₁ i ≐ σ₂ i); apply h

theorem iff_congr_subst_single : Γ ⊢ t₁ ≐ t₂ ⇒ p[↦ₛ t₁]ₚ ⇔ p[↦ₛ t₂]ₚ := by
  pintro
  apply iff_congr_subst
  intro i
  cases i using Fin.cases with simp
  | zero => passumption
  | succ i => prefl

theorem eq_subst (h : ∀ i, Γ ⊢ σ₁ i ≐ σ₂ i) : Γ ⊢ p[σ₁]ₚ ⇒ p[σ₂]ₚ := by
  papply iff_mp
  exact iff_congr_subst h

namespace Tactic

open Lean Parser Syntax Meta Elab Tactic

syntax prwRule := ("← "?) term

def prwRuleToTactic (rule : TSyntax ``prwRule) : MacroM (TSyntax ``tacticSeq) := do
  match rule with
  | `(prwRule | $n:num) => `(tacticSeq| pexact $(← hypTerm n.getNat))
  | `(prwRule | $t:term) => `(tacticSeq| pexact $t)
  | `(prwRule | ← $n:num) => `(tacticSeq| psymm; pexact $(← hypTerm n.getNat))
  | `(prwRule | ← $t:term) => `(tacticSeq| psymm; pexact $t)
  | _ => Macro.throwError "unknown syntax for prwRule {rule}"

def prwSolve (rule : TSyntax ``prwRule) (goal : MVarId) (debug? : Bool) : TacticM (List MVarId) := do
  if !(← goal.getType).isAppOf ``Proof then throwError "{(← goal.getType)} is not a proof"
  let tac ← liftMacroM (prwRuleToTactic rule)
  let prwThms := prwExt.getState (← MonadEnv.getEnv)
  let mut newGoals := []
  let mut currentGoals := [goal]
  let mut success := false
  repeat
    let goal :: currentGoals' := currentGoals | break
    if debug? then logInfo m!"prw: try to solve {(← goal.getType)}"
    currentGoals := currentGoals'
    try
      let newGoals' ← withReducibleAndInstances (evalTacticAt tac goal)
      newGoals := newGoals ++ newGoals'
      success := true
    catch _ =>
      for i in [:prwThms.size] do
        let thm := prwThms[prwThms.size-1-i]!
        try
          currentGoals := currentGoals ++ (← withReducibleAndInstances (evalTacticAt (←`(tactic| papply $(mkIdent thm))) goal))
          if debug? then logInfo m!"prw: {thm} succeed"
          break
        catch _ =>
          continue
  if !success then throwError m!"prw failed to rewrite {rule} on goal {goal}"
  return newGoals

def runPrwAtMainGoal (rules : TSyntaxArray ``prwRule) (debug? : Bool) : TacticM Unit := do
  for rule in rules do
    let rwGoal :: mainGoals ← evalTacticAt (← `(tactic| papply iff_mpr with 2)) (← getMainGoal) | throwError "prw failed"
    let newGoals ← prwSolve rule rwGoal debug?
    replaceMainGoal (mainGoals ++ newGoals)
    if debug? then logInfo m!"prw: current status {(← getMainGoal)}"

def runPrwAtLocalHyp (rules : TSyntaxArray ``prwRule) (target : TSyntax `ident) (debug? : Bool) : TacticM Unit := do
  for rule in rules do
    let rwGoal :: mainGoals ← evalTacticAt (← `(tactic| papply iff_mp at $target with 2)) (← getMainGoal) | throwError "prw failed"
    let newGoals ← prwSolve rule rwGoal debug?
    replaceMainGoal (mainGoals ++ newGoals)
    if debug? then logInfo m!"prw: current status {(← getMainGoal)}"

def runPrwAtAssumption (rules : TSyntaxArray ``prwRule) (target : ℕ) (debug? : Bool) : TacticM Unit := do
  for rule in rules do
    let [rwGoal, mainGoal] ← evalTacticAt (← `(tactic| eapply cut_append)) (← getMainGoal) | throwError "prw failed"
    let [rwGoal] ← evalTacticAt
      (← `(tactic| papply iff_mp with 2; (on_goal 2 => passumption $(mkNatLit target)))) rwGoal
      | throwError "prw failed"
    let newGoals ← prwSolve rule rwGoal debug?
    let mainGoal :: _ ← evalTacticAt (← `(tactic| (pswap 0 $(mkNatLit (target+1)); pclear 0))) mainGoal | throwError "prw failed"
    replaceMainGoal (mainGoal :: newGoals)
    if debug? then logInfo m!"prw: current status {(← getMainGoal)}"

/--
  `prw [e₁, ⋯, eₙ]` rewrites a proof goal `Γ ⊢ p` using given rules. A rule `e` can be either proof term or a
  number (the number of assumption), having type `Δ ⊢ t₁ ≐ t₂` or `Δ ⊢ q ⇔ r` (and `Δ` should be a subset of
  `Γ`). Also, `←e` reverse the direction of rewrite.
  
  - `prw [e₁, ⋯, eₙ]` will rewrite on the current goal.
  - `prw [e₁, ⋯, eₙ] at h` (where `h` is an identifier) will rewrite at local hypothesis `h`.
  - `prw [e₁, ⋯, eₙ] at n` (where `n` is a number) will rewrite on `n`-th assumption.
  
  `prw_debug` runs `prw` tactic while printing debug information.
  -/
syntax ("prw" <|> "prw_debug") "[" withoutPosition(prwRule,*,?) "]" (location)? : tactic

elab_rules : tactic
| `(tactic| prw [$rules,*]) => runPrwAtMainGoal rules.getElems false
| `(tactic| prw_debug [$rules,*]) => runPrwAtMainGoal rules.getElems true
| `(tactic| prw [$rules,*] at $h:ident) => runPrwAtLocalHyp rules.getElems h false
| `(tactic| prw_debug [$rules,*] at $h:ident) => runPrwAtLocalHyp rules.getElems h true
| `(tactic| prw [$rules,*] at $n:num) => runPrwAtAssumption rules.getElems n.getNat false
| `(tactic| prw_debug [$rules,*] at $n:num) => runPrwAtAssumption rules.getElems n.getNat true

end Tactic

theorem ne_symm : Γ ⊢ ~ t₁ ≐ t₂ ⇒ ~ t₂ ≐ t₁ := by
  pintros
  papplya 1
  prw [0]
  prefl

theorem ne_comm (t₁ t₂) : Γ ⊢ ~ t₁ ≐ t₂ ⇔ ~ t₂ ≐ t₁ := by
  papply iff_intro <;> pexact ne_symm

/-- Compactness theorem (for proofs). -/
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

variable {T : L.Theory}

theorem generalization_alls : ↑ᵀ^[n] T ⊢ p ↔ T ⊢ ∀* p := by
  induction n with simp [Formula.alls]
  | zero => rfl
  | succ n ih => rw [←shift_shiftN, generalization, ih]

theorem foralls_intro : ↑ᵀ^[n] T ⊢ p → T ⊢ ∀* p := generalization_alls.mp

theorem foralls_elim (σ : L.Subst n m) : T ⊢ ∀* p → ↑ᵀ^[m] T ⊢ p[σ]ₚ := by
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

theorem foralls_imp : T ⊢ ∀* (p ⇒ q) ⇒ ∀* p ⇒ ∀* q := by
  pintros
  apply foralls_intro
  apply mp (p := p) <;> rw [generalization_alls] <;> passumption

theorem iff_congr_foralls : T ⊢ ∀* (p ⇔ q) ⇒ ∀* p ⇔ ∀* q := by
  pintro
  papply iff_intro <;> papply foralls_imp <;> papply foralls_intro
  · papply iff_mp; rw [generalization_alls]; passumption
  · papply iff_mpr; rw [generalization_alls]; passumption

/-- The deductive closure of a theory. -/
abbrev theorems (T : L.Theory) : L.Theory := { p | T ⊢ p }

/-- A theory is decidable if its provability is decidable. -/
abbrev Decidable (T : L.Theory) := DecidablePred T.theorems

end Theory

notation Γ:50 "⊬" p:50 => ¬ Γ ⊢ p

/-- A theory (formula set in general) is consistent if it does not prove `⊥`. -/
def Consistent (Γ : L.FormulaSet n) := Γ ⊬ ⊥

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
    papplya 0
    pexact h₂
  · intro h₁ h₂
    apply h₁
    pcontra
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

/--
  A theory (formula set in general) is complete if for each `p` it either proves `p` or proves `~ p`.
  
  Note: it does not assume the theory to be consistent. -/
def Complete (Γ : L.FormulaSet n) := ∀ p, Γ ⊢ p ∨ Γ ⊢ ~ p

theorem Complete.disprovable_of_unprovable (h : Complete Γ) : Γ ⊬ p → Γ ⊢ ~ p := by
  rcases h p with h₁ | h₁ <;> simp [h₁]

theorem Complete.unprovable_iff (h₁ : Complete Γ) (h₂ : Consistent Γ) : Γ ⊬ p ↔ Γ ⊢ ~ p := by
  rcases h₁ p with h | h <;> simp [h] <;> intro h'
  · exact h₂ (h'.mp h)
  · exact h₂ (h.mp h')

def Henkin (Γ : L.FormulaSet n) := ∀ p, Γ ⊢ ∃' p → ∃ (c : L.Const), Γ ⊢ p[↦ₛ c]ₚ

end FirstOrder.Language
