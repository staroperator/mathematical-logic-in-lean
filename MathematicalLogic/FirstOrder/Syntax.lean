import MathematicalLogic.Vec
import MathematicalLogic.Notation
import MathematicalLogic.FirstOrder.Syntax.Init

/-!

# Syntax of first-order logic

This file defines the syntax of first-order logic.

## Definitions

* `Language` defines first-order languages.
* `L.Term n` and `L.Formula n` are terms and formulas for a first-order language `L`, with
  variables as well-scoped de Bruijn indexes in `Fin n`.
* `L.Subst n m`, defined as `Fin n → L.Term m`, is the parallel de Bruijn substitutions that
  substitutes `n` variables into terms in `L.Term m`.
* `Term.subst` and `Formula.subst` are substitutions of terms and formulas.
* Operations over `L.Subst`, including identical substitution `idₛ`, composition `∘ₛ`, variable
  shifting `Subst.shift`, substitution lifting `⇑ₛ` (the "up" operation in Autosubst paper),
  single variable substitution `↦ₛ`, etc.

## Equational theory

We formalize the equational theory of de Bruijn substitutions, extending the Autosubst paper with
well-scoped syntax and a much richer set of operations.

We tag the rewriting rules in Autosubst paper with the simp set `syntax_simp`. Tactic `syntax_simp`
uses these rules to rewrite FOL syntaxes to their normal forms, e.g.

```
example {L : Language} {n m : ℕ} {t : L.Term (n + 1)} {t' : L.Term n} {σ : L.Subst n m} :
    t[↦ₛ t']ₜ[σ]ₜ = t[⇑ₛσ]ₜ[↦ₛ t'[σ]ₜ]ₜ := by
  syntax_simp
```

This is not a complete decision procedure like the Autosubst paper does, though it already solves a
lot of equalities.

## Design note

* *Syntax representations.* Our definition is a nameless representation with de Bruijn index, in
  favor of its simplicity with well-defined capture-avoiding substitution. We don't want our
  syntactic definition rely on meta-level constructions (e.g. HOAS). In comparison, Mathlib's model
  theory folder uses a locally nameless representation.
* *Well-scoped syntax.* We start from a non-well-scoped design, where `L.Formula` takes any index in
  `ℕ` as its variable. Switching to well-scoped design gives some advantages:
  1. it makes definitions simpler in many cases, e.g. `FirstOrder.Language.Order` requires two
  `Formula 2` for less-equal `⪯` and less-than `≺`. In non-well-scoped design, one would require a
  formula with a proof that only `0` and `1` are used.
  2. it's easier to prove computability results, since substitutions as `ℕ → L.Term` are not
    encodable, but `Fin n → L.Term m` are.
  3. The proof system can admit empty structure (see `Proof.lean` for more details).
* *Equality.* Equality can be defined as a primitive notion (which is what we are doing) or an
  optional binary relation. The advantage to define it as a primitive notion is that we can enforce
  equalities to be interpreted as true equality, and we can provide proof tactics on equalities for
  any languages.

## References

* Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution. Steven Schäfer, Tobias Tebbi,
  Gert Smolka. <https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf>
* Completeness and Decidability of de Bruijn Substitution Algebra in Coq. Steven Schäfer, Gert
  Smolka, Tobias Tebbi. <https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Completeness.pdf>
* 1001 Representations of Syntax with Binding. Jesper Cockx. <https://jesper.sikanda.be/posts/1001-syntax-representations.html>

-/

namespace FirstOrder

attribute [syntax_simp] Nat.add_zero Nat.reduceAdd Nat.reduceAddAdd Fin.reduceSucc Fin.reduceAddNat
  Fin.reduceOfNat Fin.succ_natLit Fin.addNat_zero Fin.addNat_one Fin.addNat_succ Fin.castAdd'_zero
  Fin.castAdd'_one Fin.castAdd'_succ Vec.cons_succ Vec.head_cons Vec.tail_cons Vec.tail_apply
  Vec.cons_natLit Vec.append_left Vec.append_right Vec.nil_append Vec.cons_append
  Vec.append_natLit_left

/-- First-order language. `L.Func n` is the type of `n`-ary functions, and `L.Rel n` is the type of
  `n`-ary relations (predicates).

  Note: `Func` and `Rel` are `Type`s, since there is no need for higher universe level right now. -/
structure Language where
  Func : ℕ → Type
  Rel : ℕ → Type

namespace Language

variable {L : Language}

abbrev Const (L : Language) := L.Func 0

/-- `L.Term n` is the type of terms with variables indexed by `Fin n`. -/
inductive Term (L : Language) (n : ℕ) : Type where
  /-- A variable indexed by `Fin n`. -/
| var : Fin n → L.Term n
  /-- A function symbol applied by a vector of terms. -/
| func : L.Func m → (Fin m → L.Term n) → L.Term n

namespace Term

@[inherit_doc] prefix:max "#" => var
@[inherit_doc] infix:70 " ⬝ᶠ " => func

instance : Coe L.Const (L.Term n) := ⟨λ c => c ⬝ᶠ []ᵥ⟩

instance decEq [∀ n, DecidableEq (L.Func n)] : DecidableEq (L.Term n) := by
  intro t₁ t₂
  cases t₁ <;> cases t₂
  case var.var n m =>
    rw [var.injEq]
    by_cases h : n = m
    · exact isTrue h
    · exact isFalse h
  case func.func n f v₁ m g v₂ =>
    by_cases h : n = m
    · subst h; simp [func.injEq]; rw [Vec.ext_iff]
      have := λ i => decEq (v₁ i) (v₂ i)
      infer_instance
    · simp [h]; exact isFalse not_false
  all_goals exact isFalse Term.noConfusion

@[simp] def size : L.Term n → ℕ
| #_ => 0
| _ ⬝ᶠ v => (Vec.max λ i => (v i).size) + 1
instance : SizeOf (L.Term n) := ⟨size⟩
@[simp] theorem sizeOf_lt_func {f : L.Func m} {v : Fin m → L.Term n} {i} :
    sizeOf (v i) < sizeOf (f ⬝ᶠ v) :=
  Nat.lt_succ_of_le (Vec.le_max (v := λ i => (v i).size) i)

end Term

/-- `σ : L.Subst n m` substitutes variable `i : Fin n` into a term `σ i : L.Term m`. This is defined
  as `Fin n → L.Term m`, but `Subst.of` should be used to create substitution from raw lambdas. -/
def Subst (L : Language) (n m : ℕ) := Vec (L.Term m) n

@[ext] theorem Subst.ext {σ₁ σ₂ : L.Subst n m} : (∀ i, σ₁ i = σ₂ i) → σ₁ = σ₂ := funext

/-- Substitution of a term. -/
def Term.subst : L.Term n → L.Subst n m → L.Term m
| #i, σ => σ i
| f ⬝ᶠ v, σ => f ⬝ᶠ λ i => (v i).subst σ
@[inherit_doc Term.subst] macro:max t:term noWs "[" σ:term "]ₜ" : term => `(Term.subst $t $σ)
@[app_unexpander Term.subst] def Term.unexpandSubst : Lean.PrettyPrinter.Unexpander
| `($_ $t $σ) => `($t[$σ]ₜ)
| _ => throw ()

@[simp, syntax_simp] theorem Term.subst_var : (#i)[σ]ₜ = σ i := rfl
@[simp, syntax_simp] theorem Term.subst_func {f : L.Func k} {v : Fin k → L.Term n} :
    (f ⬝ᶠ v)[σ]ₜ = f ⬝ᶠ λ i => (v i)[σ]ₜ := rfl

theorem Term.subst_const {c : L.Const} : (c : L.Term n)[σ]ₜ = c := by
  syntax_simp [Vec.eq_nil]

def Subst.of (v : Fin n → L.Term m) : L.Subst n m := v
@[simp, syntax_simp] theorem Subst.of_apply {v : Fin n → L.Term m} : of v i = v i := rfl

/-- Identical substitution. -/
def Subst.id : L.Subst n n :=
  of λ i => #i
@[inherit_doc] notation "idₛ" => Subst.id
theorem Subst.id_def : (idₛ : L.Subst n n) = of λ i => #i := rfl
@[simp, syntax_simp] theorem Subst.id_apply : (idₛ i : L.Term n) = #i := rfl

@[simp, syntax_simp] theorem Term.subst_id (t : L.Term n) : t[idₛ]ₜ = t := by
  induction t with syntax_simp [*]

/-- Composition of substitutions. Note: the direction is opposite to `Function.comp`. -/
def Subst.comp (σ₁ : L.Subst n m) (σ₂ : L.Subst m k) : L.Subst n k :=
  of λ i => (σ₁ i)[σ₂]ₜ
@[inherit_doc] infixl:90 " ∘ₛ " => Subst.comp
theorem Subst.comp_def : σ₁ ∘ₛ σ₂ = of λ i => (σ₁ i)[σ₂]ₜ := rfl
@[simp, syntax_simp] theorem Subst.comp_apply : (σ₁ ∘ₛ σ₂) i = (σ₁ i)[σ₂]ₜ := rfl

@[syntax_simp] theorem Term.subst_subst : t[σ₁]ₜ[σ₂]ₜ = t[σ₁ ∘ₛ σ₂]ₜ := by
  induction t with syntax_simp [*]

@[syntax_simp] theorem Subst.id_comp : idₛ ∘ₛ σ = σ := by
  ext; syntax_simp
@[syntax_simp] theorem Subst.comp_id : σ ∘ₛ idₛ = σ := by
  ext; syntax_simp
@[syntax_simp] theorem Subst.comp_assoc : σ₁ ∘ₛ σ₂ ∘ₛ σ₃ = σ₁ ∘ₛ (σ₂ ∘ₛ σ₃) := by
  ext; syntax_simp
@[syntax_simp] theorem Subst.nil_comp : []ᵥ ∘ₛ σ = []ᵥ := by
  simp [Vec.eq_nil]
@[syntax_simp] theorem Subst.cons_comp : (t ∷ᵥ σ₁) ∘ₛ σ₂ = t[σ₂]ₜ ∷ᵥ σ₁ ∘ₛ σ₂ := by
  ext i; cases i using Fin.cases with syntax_simp
@[syntax_simp] theorem Subst.append_comp : (σ₁ ++ᵥ σ₂) ∘ₛ σ₃ = σ₁ ∘ₛ σ₃ ++ᵥ σ₂ ∘ₛ σ₃ := by
  ext i; cases i using Fin.addCases' with syntax_simp
@[syntax_simp] theorem Subst.of_comp {v : Fin n → L.Term m} :
    of v ∘ₛ σ = of λ i => (v i)[σ]ₜ := rfl
@[syntax_simp] theorem Subst.of_nil : (of []ᵥ : L.Subst 0 n) = []ᵥ := rfl
@[syntax_simp] theorem Subst.of_cons : of (t ∷ᵥ v) = t ∷ᵥ of v := rfl
@[syntax_simp] theorem Subst.of_append : of (v₁ ++ᵥ v₂) = of v₁ ++ᵥ of v₂ := rfl

/-- `Subst.shift k` shifts variables from `0..n-1` to `k..n-1+k`. -/
def Subst.shift (k : ℕ) : L.Subst n (n + k) :=
  of λ x => #(x.addNat k)
theorem Subst.shift_def : (shift k : L.Subst n (n + k)) = of λ x => #(x.addNat k) := rfl
@[simp, syntax_simp] theorem Subst.shift_apply :
    (shift k i : L.Term (n + k)) = #(i.addNat k) := rfl
@[syntax_simp] theorem Subst.shift_zero : (shift 0 : L.Subst n n) = idₛ := rfl

open Lean Meta Qq in
dsimproc [syntax_simp] Subst.shift_comp_shift (Subst.comp (Subst.shift _) (Subst.shift _)) := λ e => do
  let_expr Subst.comp L n _ _ σ₁ σ₂ := ← whnfR e | return .continue
  let_expr Subst.shift _ _ k₁ := ← whnfR σ₁ | return .continue
  let_expr Subst.shift _ _ k₂ := ← whnfR σ₂ | return .continue
  let some _ ← getNatValue? k₂ | return .continue
  return .continue (.some <| mkApp3 (.const ``Subst.shift []) L n (mkNatAdd k₁ k₂))

example : (Subst.shift 10 : L.Subst n (n + 10)) ∘ₛ Subst.shift 15 = Subst.shift 25 := by
  syntax_simp

/-- `↑ₜt` is the abbreviation of `t[Subst.shift 1]ₜ`. -/
notation:max "↑ₜ" t:max => t[Subst.shift 1]ₜ

/-- `↑ₜ^[k] t` is the abbreviation of `t[Subst.shift k]ₜ`. -/
notation:arg "↑ₜ^[" k "] " t:arg => t[Subst.shift k]ₜ

@[app_unexpander Term.subst] def Term.unexpandSubst' : Lean.PrettyPrinter.Unexpander
| `($_ $t $σ) =>
  match σ with
  | `(Subst.shift 1) => `(↑ₜ$t)
  | `(Subst.shift $k) => `(↑ₜ^[$k] $t)
  | σ => `($t[$σ]ₜ)
| _ => throw ()

/-- `Subst.embed k` keeps variables from `0..k-1` unchanged, but embeds them into `L.Term (n + k)`. -/
def Subst.embed (k : ℕ) : L.Subst k (n + k) :=
  of λ i => #(Fin.castAdd' i n)
theorem Subst.embed_def : (embed k : L.Subst k (n + k)) = of λ i => #(Fin.castAdd' i n) := rfl
@[simp, syntax_simp] theorem Subst.embed_apply :
    (embed k i : L.Term (n + k)) = #(Fin.castAdd' i n) := rfl
@[syntax_simp] theorem Subst.embed_zero : (embed 0 : L.Subst 0 n) = []ᵥ := by
  simp [Vec.eq_nil]
@[syntax_simp] theorem Subst.embed_succ :
    (embed (k + 1) : L.Subst (k + 1) (n + k + 1)) = #0 ∷ᵥ embed k ∘ₛ shift 1 := by
  ext i; cases i using Fin.cases <;> syntax_simp

/-- `↦ₛ t` substitutes variable `0` to `t` and shifts remained variables `i + 1` back to `i`. It is
  an abbreviation of `t ∷ᵥ id`. -/
abbrev Subst.single (t : L.Term n) : L.Subst (n + 1) n := t ∷ᵥ idₛ
@[inherit_doc] prefix:lead "↦ₛ " => Subst.single

/-- `≔ₛ t` is similar to `↦ₛ t`, but only substitutes variable `0` and does not shift others. It is
  an abbreviation of `t ∷ᵥ Subst.shift 1`. -/
abbrev Subst.assign (t : L.Term (n + 1)) : L.Subst (n + 1) (n + 1) := t ∷ᵥ shift 1
@[inherit_doc] prefix:lead "≔ₛ " => Subst.assign

-- TODO: `Subst.liftk` and `Subst.lift` shouldn't be tagged with `syntax_simp`

/-- `⇑ₛ^[k] σ` keeps variables `0..k-1` unchanged and performs substitutions on remained variables
  as if `0..k-1` are all eliminated. -/
@[syntax_simp] abbrev Subst.lift (k : ℕ) (σ : L.Subst n m) : L.Subst (n + k) (m + k) :=
  embed k ++ᵥ σ ∘ₛ shift k
@[inherit_doc] notation "⇑ₛ^[" k "] " => Subst.lift k

/-- `⇑ₛσ` is an abbreviation of `⇑ₛ^[1] σ`. -/
prefix:max "⇑ₛ" => Subst.lift 1

@[app_unexpander Subst.lift] def Subst.unexpandLift : Lean.PrettyPrinter.Unexpander
| `($_ $k $σ) =>
  match k with
  | `(1) => `(⇑ₛ$σ)
  | k => `(⇑ₛ^[$k] $σ)
| _ => throw ()

example : ⇑ₛ^[k + 1] σ 0 = #0 := by syntax_simp
example : ⇑ₛσ i.succ = ↑ₜ(σ i) := by syntax_simp
example {σ : L.Subst (n + 2) m} : ⇑ₛσ 2 = ↑ₜ(σ 1) := by syntax_simp
example : ⇑ₛ^[2] σ 1 = #1 := by syntax_simp

open Lean Meta in
simproc [syntax_simp] Subst.var_cons_shift (Vec.cons (Term.var _) (Subst.shift _)) := λ e => do
  let_expr Vec.cons term n t σ := e | return .continue
  let_expr Term.var L _ i := ← whnfD t | return .continue
  let some (i, _) := ← getOfNatValue? i ``Fin | return .continue
  let_expr Subst.shift _ _ k := σ | return .continue
  let some k := k.nat? | return .continue
  if i + 1 ≠ k then return .continue
  let e := mkApp3 (.const ``Subst.shift []) L (mkNatAdd n (mkNatLit 1)) (mkNatLit i)
  let proof := mkApp4 (.const ``Eq.symm [1])
    (mkApp2 (.const ``Vec [0]) term (mkNatAdd n (mkNatLit 1)))
    e (mkApp4 (.const ``Vec.cons [0]) term n t σ) (mkApp3 (.const ``Vec.eq_cons [0]) term n e)
  return .continue <| .some { expr := e, proof? := proof}

example : #0 ∷ᵥ Subst.shift 1 = (idₛ : L.Subst (n + 1) (n + 1)) := by syntax_simp
example : #1 ∷ᵥ Subst.shift 2 = (Subst.shift 1 : L.Subst (n + 1) (n + 2)) := by syntax_simp

theorem Subst.embed_comp_append_shift_comp (σ : L.Subst (n + k) m) :
    embed k ∘ₛ σ ++ᵥ shift k ∘ₛ σ = σ := by
  ext x; cases x using Fin.addCases' <;> syntax_simp

@[syntax_simp] theorem Subst.embed_append_shift :
    embed k ++ᵥ shift k = (idₛ : L.Subst (n + k) (n + k)) := by
  rw [← embed_comp_append_shift_comp idₛ]; syntax_simp

@[syntax_simp] theorem Subst.shift_comp_cons : shift (k + 1) ∘ₛ (t ∷ᵥ σ) = shift k ∘ₛ σ := by
  ext; syntax_simp

@[syntax_simp] theorem Subst.shift_comp_append : shift k ∘ₛ (σ₁ ++ᵥ σ₂) = σ₂ := by
  ext; syntax_simp

@[syntax_simp] theorem Subst.embed_comp_append : embed k ∘ₛ (σ₁ ++ᵥ σ₂) = σ₁ := by
  ext; syntax_simp

example : ⇑ₛ^[0] σ = σ := by syntax_simp
example : ⇑ₛ (⇑ₛ^[k] σ) = ⇑ₛ^[k + 1] σ := by syntax_simp
example : ⇑ₛ(idₛ : L.Subst n n) = idₛ := by syntax_simp
example : ⇑ₛ(σ₁ ∘ₛ σ₂) = ⇑ₛσ₁ ∘ₛ ⇑ₛσ₂ := by syntax_simp
example : Subst.shift 1 ∘ₛ ⇑ₛσ = σ ∘ₛ Subst.shift 1 := by syntax_simp
example : (↑ₜt₁)[t₂ ∷ᵥ σ]ₜ = t₁[σ]ₜ := by syntax_simp
example : (↑ₜt₁)[↦ₛ t₂]ₜ = t₁ := by syntax_simp
example : (↑ₜt₁)[≔ₛ t₂]ₜ = ↑ₜt₁ := by syntax_simp
example : (↑ₜt)[⇑ₛσ]ₜ = ↑ₜ(t[σ]ₜ) := by syntax_simp
example : t[↦ₛ t']ₜ[σ]ₜ = t[⇑ₛσ]ₜ[↦ₛ t'[σ]ₜ]ₜ := by syntax_simp
example : (↑ₜ^[m] t)[⇑ₛ^[m] σ]ₜ = ↑ₜ^[m] (t[σ]ₜ) := by syntax_simp

def Term.vars : L.Term n → Set (Fin n)
| #i => {i}
| _ ⬝ᶠ v => ⋃ i, (v i).vars

theorem Term.subst_ext_vars (h : ∀ x ∈ vars t, σ₁ x = σ₂ x) : t[σ₁]ₜ = t[σ₂]ₜ := by
  induction t with
  | var => simpa [vars] using h
  | func t v ih =>
    simp only [subst_func, func.injEq, heq_eq_eq, true_and]
    simp only [vars, Set.mem_iUnion, forall_exists_index] at h
    ext i
    apply ih
    intro
    apply h

theorem Term.vars_subst : t[σ]ₜ.vars = ⋃ x ∈ t.vars, (σ x).vars := by
  induction t with
  | var => simp [vars]
  | func t v ih =>
    simp only [subst_func, vars, Set.mem_iUnion, Set.iUnion_exists]
    rw [Set.iUnion_comm]
    simp_rw [ih]

/-- `L.Formula n` is the type of formulas with free variables indexed by `Fin n`. -/
inductive Formula (L : Language) : ℕ → Type where
  /-- A relation symbol applied by a vector of terms. -/
| rel : L.Rel m → (Fin m → L.Term n) → L.Formula n
  /-- Equality between two terms. -/
| eq : L.Term n → L.Term n → L.Formula n
| false : L.Formula n
| imp : L.Formula n → L.Formula n → L.Formula n
  /-- Universal quantification of a formula. -/
| all : L.Formula (n + 1) → L.Formula n

namespace Formula

@[inherit_doc] infix:70 " ⬝ʳ " => rel
@[inherit_doc] infix:60 " ≐ " => eq
@[inherit_doc] prefix:100 "∀' " => all

instance : ClassicalPropNotation (L.Formula n) := ⟨false, imp⟩

/-- Existential quantification of a formula. It is defined as `~ ∀' (~ p)`. -/
def ex (p : L.Formula (n + 1)) := ~ ∀' (~ p)
@[inherit_doc] prefix:100 "∃' " => ex

/-- Conjunction of a vector of formulas. -/
def vecAnd : {m : ℕ} → Vec (L.Formula n) m → L.Formula n
| 0, _ => ⊤
| _ + 1, v => v.head ⩑ vecAnd v.tail
@[inherit_doc vecAnd] notation3 "⋀ "(...)", " r:52:(scoped r => vecAnd r) => r

/-- Disjunction of a vector of formulas. -/
def vecOr : {m : ℕ} → Vec (L.Formula n) m → L.Formula n
| 0, _ => ⊥
| _ + 1, v => v.head ⩒ vecOr v.tail
@[inherit_doc vecOr] notation3 "⋁ "(...)", " r:52:(scoped r => vecOr r) => r

/-- Universal quantification of a block of `k` variables. -/
def allN : (k : ℕ) → L.Formula (n + k) → L.Formula n
| 0, p => p
| k + 1, p => allN k (∀' p)
@[inherit_doc] notation "∀^[" k "] " p:arg => allN k p

/-- Existential quantification of a block of `k` variables. -/
def exN : (k : ℕ) → L.Formula (n + k) → L.Formula n
| 0, p => p
| k + 1, p => exN k (∃' p)
@[inherit_doc] notation "∃^[" k "] " p:arg => exN k p

@[simp, syntax_simp] theorem false_eq : false = (⊥ : L.Formula n) := rfl
@[simp, syntax_simp] theorem imp_eq : imp p q = p ⇒ q := rfl
@[simp, syntax_simp] theorem neg_eq {p : L.Formula n} : (p ⇒ ⊥) = ~ p := rfl

@[simp] theorem imp_inj {p₁ q₁ p₂ q₂ : L.Formula n} : (p₁ ⇒ q₁) = p₂ ⇒ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
  iff_of_eq (imp.injEq _ _ _ _)
@[simp] theorem neg_inj {p q : L.Formula n} : ~ p = ~ q ↔ p = q := by simp [← neg_eq]

@[simp] def size : L.Formula n → ℕ
| _ ⬝ʳ _ | _ ≐ _ | ⊥ => 0
| p ⇒ q => p.size + q.size + 1
| ∀' p => p.size + 1
instance : SizeOf (L.Formula n) := ⟨size⟩
@[simp] theorem sizeOf_lt_imp_left {p q : L.Formula n} : sizeOf p < sizeOf (p ⇒ q) :=
  Nat.lt_succ_of_le (Nat.le_add_right _ _)
@[simp] theorem sizeOf_lt_imp_right {p q : L.Formula n} : sizeOf q < sizeOf (p ⇒ q) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)
@[simp] theorem sizeOf_lt_all {p : L.Formula (n + 1)} : sizeOf p < sizeOf (∀' p) :=
  Nat.lt_succ_self _

instance decEq [∀ n, DecidableEq (L.Func n)] [∀ n, DecidableEq (L.Rel n)] :
    DecidableEq (L.Formula n) := by
  intro p q
  cases p <;> cases q
  case rel.rel n r₁ v₁ m r₂ v₂ =>
    by_cases h : n = m
    · subst h; simp [rel.injEq]; rw [Vec.ext_iff]; infer_instance
    · simp [h]; exact isFalse not_false
  case eq.eq =>
    rw [eq.injEq]; infer_instance
  case false.false => exact isTrue rfl
  case imp.imp p₁ q₁ p₂ q₂ =>
    rw [imp.injEq]
    have := decEq p₁ p₂
    have := decEq q₁ q₂
    infer_instance
  case all.all p q =>
    rw [all.injEq]
    exact decEq p q
  all_goals exact isFalse Formula.noConfusion

/-- Substitution of a formula. -/
def subst : L.Formula n → L.Subst n m → L.Formula m
| r ⬝ʳ v, σ => r ⬝ʳ λ i => (v i)[σ]ₜ
| t₁ ≐ t₂, σ => t₁.subst σ ≐ t₂.subst σ
| ⊥, _ => ⊥
| p ⇒ q, σ => p.subst σ ⇒ q.subst σ
| ∀' p, σ => ∀' (p.subst ⇑ₛσ)
@[inherit_doc subst] macro:max p:term noWs "[" σ:term "]ₚ" : term => `(subst $p $σ)
@[app_unexpander subst] def unexpandSubst : Lean.PrettyPrinter.Unexpander
| `($_ $p $σ) => `($p[$σ]ₚ)
| _ => throw ()

@[simp, syntax_simp] theorem subst_rel : (r ⬝ʳ ts)[σ]ₚ = r ⬝ʳ λ i => (ts i)[σ]ₜ := rfl
@[simp, syntax_simp] theorem subst_eq : (t₁ ≐ t₂)[σ]ₚ = t₁[σ]ₜ ≐ t₂[σ]ₜ := rfl
@[simp, syntax_simp] theorem subst_false : ⊥[σ]ₚ = ⊥ := rfl
@[simp, syntax_simp] theorem subst_imp : (p ⇒ q)[σ]ₚ = p[σ]ₚ ⇒ q[σ]ₚ := rfl
@[simp, syntax_simp] theorem subst_true : ⊤[σ]ₚ = ⊤ := rfl
@[simp, syntax_simp] theorem subst_neg : (~ p)[σ]ₚ = ~ p[σ]ₚ := rfl
@[simp, syntax_simp] theorem subst_and : (p ⩑ q)[σ]ₚ = p[σ]ₚ ⩑ q[σ]ₚ := rfl
@[simp, syntax_simp] theorem subst_or : (p ⩒ q)[σ]ₚ = p[σ]ₚ ⩒ q[σ]ₚ := rfl
@[simp, syntax_simp] theorem subst_iff : (p ⇔ q)[σ]ₚ = p[σ]ₚ ⇔ q[σ]ₚ := rfl
@[simp, syntax_simp] theorem subst_all : (∀' p)[σ]ₚ = ∀' (p[⇑ₛσ]ₚ) := rfl
@[simp, syntax_simp] theorem subst_ex : (∃' p)[σ]ₚ = ∃' (p[⇑ₛσ]ₚ) := rfl

@[simp, syntax_simp] theorem subst_vecAnd {v : Vec (L.Formula n) m} :
    (⋀ i, v i)[σ]ₚ = ⋀ i, (v i)[σ]ₚ := by
  induction m with simp [vecAnd, Vec.head, Vec.tail, Function.comp_def, *]
@[simp, syntax_simp] theorem subst_vecOr {v : Vec (L.Formula n) m} :
    (⋁ i, v i)[σ]ₚ = ⋁ i, (v i)[σ]ₚ := by
  induction m with simp [vecOr, Vec.head, Vec.tail, Function.comp_def, *]
@[simp, syntax_simp] theorem subst_allN : (∀^[k] p)[σ]ₚ = ∀^[k] (p[⇑ₛ^[k] σ]ₚ) := by
  induction k with syntax_simp [*, allN]
@[simp, syntax_simp] theorem subst_exN : (∃^[k] p)[σ]ₚ = ∃^[k] (p[⇑ₛ^[k] σ]ₚ) := by
  induction k with syntax_simp [*, exN]

@[syntax_simp] theorem subst_id (p : L.Formula n) : p[Subst.id]ₚ = p := by
  induction p with syntax_simp [*]
@[syntax_simp] theorem subst_subst {σ₁ : L.Subst n m} {σ₂ : L.Subst m k} :
    p[σ₁]ₚ[σ₂]ₚ = p[σ₁ ∘ₛ σ₂]ₚ := by
  induction p generalizing m k with syntax_simp [*]

def exUnique (p : L.Formula (n + 1)) :=
  ∃' (p ⩑ ∀' (p[⇑ₛ(Subst.shift 1)]ₚ ⇒ #0 ≐ #1))
prefix:100 "∃!' " => exUnique

@[simp, syntax_simp] theorem subst_exUnique : (∃!' p)[σ]ₚ = ∃!' p[⇑ₛσ]ₚ := by
  syntax_simp [exUnique]

/-- `↑ₚp` is the abbreviation of `p[Subst.shift 1]ₚ`. -/
notation:max "↑ₚ" p:max => p[Subst.shift 1]ₚ

/-- `↑ₚ^[k] p` is the abbreviation of `p[Subst.shift k]ₚ`. -/
notation:arg "↑ₚ^[" k "] " p:arg => p[Subst.shift k]ₚ

@[app_unexpander subst] def unexpandSubst' : Lean.PrettyPrinter.Unexpander
| `($_ $p $σ) =>
  match σ with
  | `(Subst.shift 1) => `(↑ₚ$p)
  | `(Subst.shift $k) => `(↑ₚ^[$k] $p)
  | σ => `($p[$σ]ₚ)
| _ => throw ()

example : (↑ₚp)[t ∷ᵥ σ]ₚ = p[σ]ₚ := by syntax_simp
example : (↑ₚp)[↦ₛ t]ₚ = p := by syntax_simp
example : (↑ₚp)[≔ₛ t]ₚ = ↑ₚp := by syntax_simp
example : (↑ₚp)[⇑ₛσ]ₚ = ↑ₚ(p[σ]ₚ) := by syntax_simp
example : p[↦ₛ t]ₚ[σ]ₚ = p[⇑ₛσ]ₚ[↦ₛ t[σ]ₜ]ₚ := by syntax_simp

def free : L.Formula n → Set (Fin n)
| _ ⬝ʳ v => ⋃i, (v i).vars
| t₁ ≐ t₂ => t₁.vars ∪ t₂.vars
| ⊥ => ∅
| p ⇒ q => p.free ∪ q.free
| ∀' p => { x | x.succ ∈ p.free }

theorem subst_ext_free {p : L.Formula n} {σ₁ σ₂ : L.Subst n m} :
  (∀ x ∈ p.free, σ₁ x = σ₂ x) → p[σ₁]ₚ = p[σ₂]ₚ := by
  intro h
  induction p generalizing m with
  | rel =>
    simp only [subst_rel, rel.injEq, heq_eq_eq, true_and]
    simp only [free, Set.mem_iUnion, forall_exists_index] at h
    ext i
    apply Term.subst_ext_vars
    intro
    apply h
  | eq =>
    simp only [subst_eq, eq.injEq]
    constructor <;> apply Term.subst_ext_vars <;> intros _ h' <;> apply h <;> simp [free, h']
  | false =>
    rfl
  | imp p q ih₁ ih₂ =>
    simp only [imp_eq, subst_imp, imp_inj]
    constructor <;> apply_assumption <;> intros _ h' <;> apply h <;> simp [free, h']
  | all _ ih =>
    simp only [subst_all, all.injEq]
    apply ih
    intro x h'
    cases x using Fin.cases with
    | zero =>
      rfl
    | succ x =>
      apply congr_arg (↑ₜ ·)
      apply h
      simp [free, h']

theorem free_subst {σ : L.Subst n m} :
  p[σ]ₚ.free = ⋃ x ∈ p.free, (σ x).vars := by
  induction p generalizing m with
  | rel =>
    simp only [subst_rel, free, Term.vars_subst, Set.mem_iUnion, Set.iUnion_exists]
    rw [Set.iUnion_comm]
  | eq =>
    simp [free, Term.vars_subst, Set.iUnion_or, Set.iUnion_union_distrib]
  | false =>
    simp [free]
  | imp p q ih₁ ih₂ =>
    simp only [imp_eq, subst_imp, free, Set.mem_union]
    simp_rw [Set.iUnion_or]
    rw [ih₁, ih₂, Set.iUnion_union_distrib]
  | all p ih =>
    simp only [subst_all, free, Set.mem_setOf_eq]
    ext x
    simp only [ih, Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, h₁, h₂⟩
      cases y using Fin.cases with
      | zero =>
        simp [Term.vars] at h₂
      | succ y =>
        syntax_simp [Term.vars_subst, Set.mem_iUnion, exists_prop] at h₂
        rcases h₂ with ⟨z, h₂, h₃⟩
        simp only [Term.vars, Set.mem_singleton_iff, Fin.succ_inj] at h₃
        subst h₃
        exists y
    · rintro ⟨y, ⟨h₁, h₂⟩⟩
      exists y.succ
      constructor
      · exact h₁
      · syntax_simp [Term.vars_subst, Set.mem_iUnion, exists_prop]
        exists x

end Formula

/-- A sentence is a closed formula (formula with no free variables). -/
abbrev Sentence (L : Language) := L.Formula 0

theorem Sentence.subst_nil {p : L.Sentence} {σ : L.Subst 0 0} : p[σ]ₚ = p := by
  rw [Vec.eq_nil σ, ← Vec.eq_nil idₛ, Formula.subst_id]

/-- The universal closure of a formula. -/
def Formula.alls : {n : ℕ} → L.Formula n → L.Sentence
| 0, p => p
| _ + 1, p => alls (∀' p)
prefix:100 "∀* " => Formula.alls

/-- An abbreviation of `Set (L.Formula n)`. -/
abbrev FormulaSet (L : Language) (n : ℕ) := Set (L.Formula n)

/-- `append Γ p` is the same as `insert p Γ`, but with a nicer notation `Γ,' p` so that when writing
  proofs, `Γ,' p₁,' ⋯,' pₙ` looks like a list of local hypotheses. -/
def FormulaSet.append (Γ : L.FormulaSet n) (p : L.Formula n) := insert p Γ
infixl:51 ",' " => FormulaSet.append

theorem FormulaSet.append_comm : Γ,' p,' q = Γ,' q,' p := Set.insert_comm _ _ _
theorem FormulaSet.append_eq_append : Γ = Δ → Γ,' p = Δ,' p := by intro h; rw [h]
theorem FormulaSet.subset_of_eq {Γ : L.FormulaSet n} : Γ = Δ → Γ ⊆ Δ := by intro h; rw [h]
theorem FormulaSet.mem_append : p ∈ Γ,' p := Set.mem_insert _ _
theorem FormulaSet.subset_append : Γ ⊆ Γ,' p := Set.subset_insert _ _
theorem FormulaSet.append_subset_append : Γ ⊆ Δ → Γ,' p ⊆ Δ,' p := Set.insert_subset_insert

def FormulaSet.shift (k : ℕ) (Γ : L.FormulaSet n) : L.FormulaSet (n + k) :=
  (↑ₚ^[k] ·) '' Γ
notation "↑ᴳ^[" k "]" => FormulaSet.shift k
@[simp, syntax_simp] theorem FormulaSet.shift_empty : ↑ᴳ^[k] (∅ : L.FormulaSet n) = ∅ :=
  Set.image_empty _
@[simp, syntax_simp] theorem FormulaSet.shift_append : ↑ᴳ^[k] (Γ,' p) = ↑ᴳ^[k] Γ,' ↑ₚ^[k] p :=
  Set.image_insert_eq
@[simp, syntax_simp] theorem FormulaSet.shift_zero : ↑ᴳ^[0] Γ = Γ := by
  simp [syntax_simp, FormulaSet.shift]

prefix:max "↑ᴳ" => FormulaSet.shift 1
@[simp, syntax_simp] theorem FormulaSet.shift_shift : ↑ᴳ (↑ᴳ^[k] Γ) = ↑ᴳ^[k + 1] Γ := by
  simp [syntax_simp, FormulaSet.shift, Set.image_image]

/-- A theory is a set of sentences, as the axioms of the theory (not the deductive closure). -/
abbrev Theory (L : Language) := Set L.Sentence

def Theory.shiftT : (n : ℕ) → L.Theory → L.FormulaSet n
| 0, T => T
| n + 1, T => ↑ᴳ(T.shiftT n)
notation "↑ᵀ^[" n "]" => Theory.shiftT n

@[simp, syntax_simp] theorem Theory.shiftT_zero : ↑ᵀ^[0] T = T := rfl
@[simp, syntax_simp] theorem Theory.shift_shiftT : ↑ᴳ(↑ᵀ^[n] T) = ↑ᵀ^[n + 1] T := rfl
@[simp, syntax_simp] theorem Theory.shiftk_shiftT : ↑ᴳ^[m] (↑ᵀ^[n] T) = ↑ᵀ^[n + m] T := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [← FormulaSet.shift_shift, ih, shift_shiftT]; rfl
@[simp, syntax_simp] theorem Theory.shift_eq : ↑ᴳT = ↑ᵀ^[1] T := shift_shiftT
@[simp, syntax_simp] theorem Theory.shiftk_eq : ↑ᴳ^[n] T = ↑ᵀ^[0 + n] T := shiftk_shiftT

open Std Lean.Parser

class Repr (L : Language) where
  reprFunc : L.Func n → ℕ → (Fin n → ℕ → Format) → Format
  reprRel : L.Rel n → ℕ → (Fin n → ℕ → Format) → Format

variable [Repr L]

private def reprTerm : L.Term n → ℕ → Format
| #i, _ => "#" ++ repr i
| f ⬝ᶠ v, prec => Repr.reprFunc f prec λ i => reprTerm (v i)

instance : _root_.Repr (L.Term n) := ⟨reprTerm⟩

private def reprFormula : L.Formula n → ℕ → Format
| r ⬝ʳ v, prec =>
  Repr.reprRel r prec λ i => reprTerm (v i)
| t₁ ≐ t₂, prec =>
  (if prec ≥ 60 then Format.paren else id) (reprTerm t₁ 60 ++ " = " ++ reprTerm t₂ 60)
| (∀' (p ⇒ ⊥)) ⇒ ⊥, prec =>
  (if prec ≥ 100 then Format.paren else id) ("∃ " ++ reprFormula p 100)
| (p ⇒ q ⇒ ⊥) ⇒ ⊥, prec =>
  (if prec ≥ 57 then Format.paren else id) (reprFormula p 57 ++ " ∧ " ++ reprFormula q 57)
| (p ⇒ q) ⇒ ⊥, prec =>
  (if prec ≥ 56 then Format.paren else id) (reprFormula p 56 ++ " ∨ " ++ reprFormula q 56)
| ⊥ ⇒ ⊥, _ =>
  "⊤"
| p ⇒ ⊥, prec =>
  (if prec ≥ 58 then Format.paren else id) ("~ " ++ reprFormula p 58)
| ⊥, _ =>
  "⊥"
| p ⇒ q, prec =>
  (if prec ≥ 55 then Format.paren else id) (reprFormula p 55 ++ " ⇒ " ++ reprFormula q 55)
| ∀' p, prec =>
  (if prec ≥ 100 then Format.paren else id) ("∀ " ++ reprFormula p 100)

instance : _root_.Repr (L.Formula n) := ⟨reprFormula⟩

end FirstOrder.Language
