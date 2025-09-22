# Mathematical Logic in Lean

## Formalized results

The following results are formalized in this library:

Completeness and incompleteness
- Gödel's completeness theorem
  ```lean
  theorem FirstOrder.Language.completeness {n : ℕ} {L : Language} {Γ : L.FormulaSet n} {p : L.Formula n} : Γ ⊨ p → Γ ⊢ p
  ```
- Representation theorem in Q
  ```lean
  theorem FirstOrder.Language.Theory.Q.enumerable_iff_weakly_representable {α} [Encodable α] {s : Set α}
    {T : peano.Theory} [Recursive T] [Q ⊆ᵀ T] (h : OmegaConsistent T) :
    IsEnumerable s ↔ ∃ p, ∀ (x : α), x ∈ s ↔ T ⊢ p[[⌜x⌝]ᵥ]ₚ
  theorem FirstOrder.Language.Theory.Q.recursive_iff_strongly_representable {α} [Encodable α] {s : Set α}
    {T : peano.Theory} [Recursive T] [Q ⊆ᵀ T] (h : Consistent T) :
    IsRecursive s ↔ ∃ p, (∀ x ∈ s, T ⊢ p[[⌜x⌝]ᵥ]ₚ) ∧ ∀ x ∉ s, T ⊢ ~ p[[⌜x⌝]ᵥ]ₚ
  ```
- Categoricity of second order arithmetic and real numbers
  ```lean
  theorem SecondOrder.Language.Theory.PA₂.iso_Nat (M : PA₂.Model) : Nonempty (M.toStructure ≃ᴹ Structure.of ℕ)
  theorem SecondOrder.Language.Theory.Real.iso_Real (M : Real.Model) : Nonempty (M.toStructure ≃ᴹ Structure.of ℝ)
  ```
- Quasi-categoricity of second order ZF
  ```lean
  theorem SecondOrder.Language.Theory.ZF₂.iso_V (M : ZF₂.Model) : ∃ κ, _root_.Nonempty (M.toStructure ≃ᴹ Structure.of (V κ))
  ```

TBD: Gödel's incompleteness theorems.

## Writing pure syntatic proofs

A main part of this library is an experiment of writing *pure syntactic proofs* in first-order
logic, with help of Lean's metaprogramming framework.

We first define the synatx of first-order logic with de Bruijn indexes and substitutions, and
formalize the equation theory of de Bruijn substitutions following [autosubst](https://www.ps.uni-saarland.de/Publications/documents/SchaeferEtAl_2015_Autosubst_-Reasoning.pdf).

```lean
inductive Term (L : Language) (n : ℕ) : Type where
| var : Fin n → L.Term n
| func : L.Func m → (Fin m → L.Term n) → L.Term n

inductive Formula (L : Language) : ℕ → Type where
| rel : L.Rel m → (Fin m → L.Term n) → L.Formula n
| eq : L.Term n → L.Term n → L.Formula n
| false : L.Formula n
| imp : L.Formula n → L.Formula n → L.Formula n
| all : L.Formula (n + 1) → L.Formula n
```

We define a Hilbert proof system for first-order logic:

```lean
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

inductive Proof (Γ : L.FormulaSet n) : L.Formula n → Prop where
| hyp : p ∈ Γ → Proof Γ p
| ax : p ∈ L.Axiom → Proof Γ p
| mp : Proof Γ (p ⇒ q) → Proof Γ p → Proof Γ q
```

Based on this defintion, we provide a few tactics to write proofs, including `papply` to apply
implications and `prw` to rewrite equalities/iffs. Here is a demonstration on writing pure syntatic
proof:

```lean
theorem PA.le_add_of_le_left {n : ℕ} {t t₁ t₂ : peano.Term n} :
    ↑ᵀ^[n] PA ⊢ t₁ ⪯ t₂ ⇒ t₁ ⪯ t + t₂ := by
  pintro
  -- ↑ᵀ^[n] PA,' t₁ ⪯ t₂ ⊢ t₁ ⪯ t + t₂
  prw [← zero_add t₁]
  -- ↑ᵀ^[n] PA,' t₁ ⪯ t₂ ⊢ 0 + t₁ ⪯ t + t₂
  papply add_le_add
  · -- ↑ᵀ^[n] PA,' t₁ ⪯ t₂ ⊢ 0 ⪯ t
    pexact zero_le
  · -- ↑ᵀ^[n] PA,' t₁ ⪯ t₂ ⊢ t₁ ⪯ t₂
    passumption
```

See [`Proof.lean`](MathematicalLogic/FirstOrder/Proof.lean) for the proof system and tactics. We
prove the representation theorem in such a syntatic way (and plan to prove Gödel's incompleteness
theorems syntatically also).
