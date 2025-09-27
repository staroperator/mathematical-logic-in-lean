import MathematicalLogic.FirstOrder.Computability
import MathematicalLogic.FirstOrder.Theories.Peano.BetaFunction

/-!

# Representation theorem

This file formalizes **Representation Theorem**.

1. In the first part, we prove one direction, that any partial recursive function is weakly
  representable in `Q` (`rep_iff_of_mem`). Moreover, in `PA` we prove the uniqueness (`rep_unique`)
  and the totality of primitive recursive functions (`repPrim_total`).
2. In the second part, we prove the converse direction, that any weakly representable relation is
  enumerable in ω-consistent extension of `Q` (`enumerable_iff_weakly_representable`), and any
  strongly representable relation is recursive in consistent extension of `Q`
  (`recursive_iff_strongly_representable`). Note that the ω-consistency condition in the former can
  be weakened to consistency, but to prove that we need Gödel's fixed point construction and
  Rosser's trick -- we will prove that in future.

-/

namespace FirstOrder.Language

namespace peano

/-- The representation formula of a partial recursive function. -/
@[irreducible] def rep : Partrec n → peano.Formula (n + 1)
| .const m => #0 ≐ m
| .succ => #0 ≐ S #1
| .proj i => #0 ≐ #i.succ
| .comp (n := k) f g =>
  ∃^[k] (
    (⋀ i, (rep (g i))[#(i.castAdd' (n + 1)) ∷ᵥ Subst.shift 1 ∘ₛ Subst.shift k]ₚ)
    ⩑ (rep f)[#(Fin.addNat 0 k) ∷ᵥ Subst.embed k]ₚ)
| .prec f g =>
  ∃' (
    ∃' ((rep f)[#0 ∷ᵥ Subst.shift 4]ₚ ⩑ beta #0 #1 0)
    ⩑ ∀[≺ #2] ∃' ∃' ((rep g)[#0 ∷ᵥ #2 ∷ᵥ #1 ∷ᵥ Subst.shift 6]ₚ ⩑ beta #1 #3 #2 ⩑ beta #0 #3 (S #2))
    ⩑ beta #1 #0 #2
    -- to make `rep` weakly representable in `Q`, we have to add this annoying minimization condition
    ⩑ ∀[≺ #0] (
      ∃' ((rep f)[#0 ∷ᵥ Subst.shift 5]ₚ ⩑ nbeta #0 #1 0)
      ⩒ ∃[≺ #3] ∃' ∃' ((rep g)[#0 ∷ᵥ #2 ∷ᵥ #1 ∷ᵥ Subst.shift 7]ₚ ⩑ beta #1 #3 #2 ⩑ nbeta #0 #3 (S #2))))
| .mu f =>
  (∃' ((rep f)[≔ₛ S #0]ₚ)) ⩑ ∀[≺ #0] (rep f)[0 ∷ᵥ #0 ∷ᵥ Subst.shift 2]ₚ

theorem rep_const : (rep (.const m) : peano.Formula (n + 1)) = #0 ≐ m := by
  with_unfolding_all rfl

theorem rep_succ : rep .succ = #0 ≐ S #1 := by
  with_unfolding_all rfl

theorem rep_proj : rep (.proj i) = #0 ≐ #i.succ := by
  with_unfolding_all rfl

theorem rep_comp :
    rep (.comp (n := k) (m := n) f g) = ∃^[k] (
      (⋀ i, (rep (g i))[#(i.castAdd' (n + 1)) ∷ᵥ Subst.shift 1 ∘ₛ Subst.shift k]ₚ)
      ⩑ (rep f)[#(Fin.addNat 0 k) ∷ᵥ Subst.embed k]ₚ) := by
  with_unfolding_all rfl

theorem rep_prec :
    rep (.prec f g) = ∃' (
      ∃' ((rep f)[#0 ∷ᵥ Subst.shift 4]ₚ ⩑ beta #0 #1 0)
      ⩑ ∀[≺ #2] ∃' ∃' ((rep g)[#0 ∷ᵥ #2 ∷ᵥ #1 ∷ᵥ Subst.shift 6]ₚ ⩑ beta #1 #3 #2 ⩑ beta #0 #3 (S #2))
      ⩑ beta #1 #0 #2
      ⩑ ∀[≺ #0] (
        ∃' ((rep f)[#0 ∷ᵥ Subst.shift 5]ₚ ⩑ nbeta #0 #1 0)
        ⩒ ∃[≺ #3] ∃' ∃' ((rep g)[#0 ∷ᵥ #2 ∷ᵥ #1 ∷ᵥ Subst.shift 7]ₚ ⩑ beta #1 #3 #2 ⩑ nbeta #0 #3 (S #2)))) := by
  with_unfolding_all rfl

theorem rep_mu :
    rep (.mu f) = (∃' ((rep f)[≔ₛ S #0]ₚ)) ⩑ ∀[≺ #0] (rep f)[0 ∷ᵥ #0 ∷ᵥ Subst.shift 2]ₚ := by
  with_unfolding_all rfl

abbrev repPrim (f : Primrec n) := rep (.ofPrim f)

theorem Sigma₁.rep : Sigma₁ (rep f) := by
  induction f <;> simp only [rep_const, rep_succ, rep_proj, rep_comp, rep_prec, rep_mu] <;> aesop

def repRel (f : Partrec n) : peano.Formula n :=
  ∃' ((rep f)[≔ₛ S #0]ₚ)

theorem Sigma₁.repRel : Sigma₁ (repRel f) := ex (subst rep)

end peano

theorem Proof.existsN_andN_of_andN_exists {L : Language} {Γ : L.FormulaSet n}
    {v : Vec (L.Formula (n + 1)) m} :
    Γ ⊢ (⋀ i, ∃' v i) ⇒ ∃^[m] (⋀ i, (v i)[#(i.castAdd' n) ∷ᵥ Subst.shift m]ₚ) := by
  induction m with syntax_simp [Formula.exN, Formula.vecAnd, Vec.head, Vec.tail, Function.comp_def]
  | zero => pintro; pexact true_intro
  | succ m ih =>
    pintro
    papply existsN_elim
    · papply ih
      apply andN_intro
      intro i
      papply and_right at 0
      papply andN_elim i at 0
      passumption 0
    · apply forallN_intro
      pintro
      syntax_simp
      papply existsN_intro λ i => #(i.castAdd' n)
      papply exists_elim
      · papply and_left at 1
        passumption 1
      · pintros 2
        papply exists_intro #0
        syntax_simp
        papply and_intro
        · passumption 0
        · apply andN_intro
          intro i
          papply andN_elim i at 1
          passumption 1

namespace Theory

open peano Proof

namespace Q

theorem rep_iff_of_mem {f : Partrec n} (h : m ∈ f v) :
    ↑ᵀ^[k] Q ⊢ (rep f)[t ∷ᵥ Subst.of λ i => v i]ₚ ⇔ t ≐ m := by
  classical
  induction f generalizing k m t with
  | const m =>
    simp only [Partrec.zero_eval, Part.mem_some_iff] at h
    syntax_simp [h, rep_const]
    prefl
  | succ =>
    simp only [Partrec.succ_eval, Nat.succ_eq_add_one, Part.mem_some_iff, Vec.head] at h
    syntax_simp [h, rep_succ]
    prefl
  | proj i =>
    simp only [Partrec.proj_eval, Part.mem_some_iff] at h
    syntax_simp [h, rep_proj]
    prefl
  | comp f g ih₁ ih₂ =>
    simp only [Partrec.comp_eval, Part.bind_eq_bind, Part.mem_bind_iff, Part.mem_bindVec_iff] at h
    rcases h with ⟨u, h₁, h₂⟩
    syntax_simp [rep_comp]
    papply iff_intro
    · papply existsN_elim'
      apply forallN_intro
      syntax_simp
      prw [and_imp_iff]
      pintros
      prw [←ih₁ h₂]
      papply eq_subst'
      · passumption
      · apply andN_intro
        intro i
        cases i using Fin.cases with syntax_simp
        | zero =>
          prefl
        | succ i =>
          papply andN_elim i at 1
          prw [←ih₂ i (h₁ i)]
          passumption
    · pintro
      papply existsN_intro (Subst.of λ i => u i)
      syntax_simp
      papply and_intro
      · apply andN_intro
        intro i
        prw [ih₂ i (h₁ i)]
        prefl
      · prw [ih₁ h₂]
        passumption
  | prec f g ih₁ ih₂ =>
    simp only [Partrec.prec_eval, Part.coe_some, Part.bind_eq_bind, Part.bind_some] at h
    rw [Vec.eq_cons v]
    generalize v.head = l, v.tail = v at h ⊢
    let w : Vec ℕ (l + 1) := λ i =>
      ((f.eval v).natrec (fun n ih => g.eval (n ∷ᵥ ih ∷ᵥ v)) i).get
        (Part.natrec_dom_le (Part.dom_of_mem h) (Nat.le_of_lt_succ i.isLt))
    have hw : ∀ (i : Fin (l + 1)), w i ∈ (f.eval v).natrec (fun n ih => g.eval (n ∷ᵥ ih ∷ᵥ v)) i := by
      intro i; simp [w]; apply Part.get_mem
    apply Part.mem_unique (hw ⟨l, Nat.lt_succ_self _⟩) at h
    let a := Nat.find (p := λ a => ∀ i hi, Nat.beta a i = w ⟨i, hi⟩) ⟨w.unbeta, λ i hi => Vec.beta_unbeta w ⟨i, hi⟩⟩
    have ha : ∀ i hi, Nat.beta a i = w ⟨i, hi⟩ := Nat.find_spec (p := λ a => ∀ i hi, Nat.beta a i = w ⟨i, hi⟩) _
    syntax_simp [rep_prec]
    papply iff_intro
    · papply exists_elim'
      pintro
      syntax_simp
      prw [and_imp_iff, and_imp_iff, and_imp_iff]
      pintros
      psuffices #0 ≐ a
      · prw [0, beta_ofNat] at 2; prw [2]
        rw [ha l (Nat.lt_succ_self _), h]
        prefl
      · prw [← double_neg_iff, ne_ofNat_iff, lt_ofNat_iff]
        papply or_elim'
        · papply orN_elim'
          intro ⟨b, hb⟩
          apply Nat.find_min at hb
          simp only [not_forall] at hb
          pintro
          cases hb' : Nat.find hb with
          | zero =>
            simp only [Nat.find_eq_zero, Fin.zero_eta, lt_add_iff_pos_left, add_pos_iff,
              zero_lt_one, or_true, exists_const] at hb'
            papply exists_elim
            · passumption 4
            · pintro
              prw [and_imp_iff]
              pintros
              simp_vec
              syntax_simp [← ofNat_zero]
              prw [ih₁ (hw 0)] at 1
              prw [1, 2, beta_ofNat] at 0
              papply ne_ofNat (Ne.symm hb') at 0
              passumption
          | succ i =>
            simp [Nat.find_eq_iff] at hb'
            rcases hb' with ⟨⟨hi, hi'⟩, hi''⟩
            specialize hi'' i (Nat.lt_succ_self _) (Nat.lt_succ_of_lt hi)
            papply forall_elim i at 3
            syntax_simp
            papply exists_elim
            · papplya 3; pexact lt_ofNat hi
            · pintro
              syntax_simp
              papply exists_elim'
              pintro
              prw [and_imp_iff, and_imp_iff]
              pintros
              simp_vec
              syntax_simp [← ofNat_succ]
              prw [3, beta_ofNat] at 1
              rw [hi'']
              have := hw ⟨i + 1, Nat.succ_lt_succ hi⟩
              simp only [Part.natrec_succ, Part.bind_eq_bind, Part.mem_bind_iff] at this
              rcases this with ⟨_, h, this⟩
              apply Part.mem_unique (hw ⟨i, Nat.lt_succ_of_lt hi⟩) at h; subst h
              apply ih₂ (k := k + 3) (t := #0) at this
              simp_vec at this
              syntax_simp at this
              prw [1, this] at 2
              prw [2, 3, beta_ofNat] at 0
              papply ne_ofNat (Ne.symm hi') at 0
              passumption
        · pintro
          papply forall_elim a at 1
          syntax_simp
          papplya 1 at 0
          pclear 1
          prw [bdex_ofNat_iff] at 0
          syntax_simp
          prevert
          papply or_elim'
          · papply exists_elim'
            pintro
            prw [and_imp_iff]
            pintros
            simp_vec
            syntax_simp [← ofNat_zero]
            prw [ih₁ (hw 0)] at 1
            prw [1, nbeta_ofNat] at 0
            papplya 0; rw [ha 0 (Nat.zero_lt_succ _)]
            prefl
          · papply orN_elim'
            intro ⟨i, hi⟩
            syntax_simp
            papply exists_elim'
            pintro
            papply exists_elim'
            pintro
            prw [and_imp_iff, and_imp_iff]
            pintros
            simp_vec
            syntax_simp [← ofNat_succ]
            prw [beta_ofNat] at 1
            rw [ha i (Nat.lt_succ_of_lt hi)]
            have := hw ⟨i + 1, Nat.succ_lt_succ hi⟩
            simp only [Part.natrec_succ, Part.bind_eq_bind, Part.mem_bind_iff] at this
            rcases this with ⟨_, h, this⟩
            apply Part.mem_unique (hw ⟨i, Nat.lt_succ_of_lt hi⟩) at h
            subst h
            apply ih₂ at this
            simp_vec at this
            syntax_simp at this
            prw [1, this] at 2
            prw [2, nbeta_ofNat] at 0
            papplya 0
            rw [ha (i + 1) (Nat.succ_lt_succ hi)]
            prefl
    · pintro
      papply exists_intro a
      syntax_simp
      papply and_intro
      · papply exists_intro (w 0)
        simp_vec
        syntax_simp
        papply and_intro
        · prw [ih₁ (hw 0)]; prefl
        · rw [← ofNat_zero]; prw [beta_ofNat]; rw [ha 0 (Nat.zero_lt_succ _)]; prefl
      papply and_intro
      · prw [bdall_ofNat_iff]
        apply andN_intro
        intro ⟨i, hi⟩
        papply exists_intro (w ⟨i, Nat.lt_succ_of_lt hi⟩)
        papply exists_intro (w ⟨i + 1, Nat.succ_lt_succ hi⟩)
        simp_vec
        syntax_simp
        papply and_intro
        · have := hw ⟨i + 1, Nat.succ_lt_succ hi⟩
          simp only [Part.natrec_succ, Part.bind_eq_bind, Part.mem_bind_iff] at this
          rcases this with ⟨a, h, this⟩
          apply Part.mem_unique (hw ⟨i, Nat.lt_succ_of_lt hi⟩) at h
          subst h
          apply ih₂ at this
          simp_vec at this
          syntax_simp at this
          prw [this]
          prefl
        papply and_intro
        · prw [beta_ofNat]; rw [ha i (Nat.lt_succ_of_lt hi)]; prefl
        · rw [←ofNat_succ]; prw [beta_ofNat]; rw [ha (i + 1) (Nat.succ_lt_succ hi)]; prefl
      papply and_intro
      · prw [0, beta_ofNat]; rw [ha l (Nat.lt_succ_self _), h]; prefl
      · prw [bdall_ofNat_iff]
        apply andN_intro
        intro ⟨b, hb⟩
        apply Nat.find_min at hb
        simp only [not_forall] at hb
        cases hb' : Nat.find hb with
        | zero =>
          simp only [Nat.find_eq_zero, Fin.zero_eta, lt_add_iff_pos_left, add_pos_iff, zero_lt_one,
            or_true, exists_const] at hb'
          papply or_inl
          papply exists_intro (w 0)
          simp_vec
          syntax_simp
          papply and_intro
          · prw [ih₁ (hw 0)]; prefl
          · rw [←ofNat_zero]; prw [nbeta_ofNat]; pexact ne_ofNat (Ne.symm hb')
        | succ i =>
          simp only [Nat.find_eq_iff, add_lt_add_iff_right, not_exists, Decidable.not_not] at hb'
          rcases hb' with ⟨⟨hi, hi'⟩, hi''⟩
          specialize hi'' i (Nat.lt_succ_self _) (Nat.lt_succ_of_lt hi)
          papply or_inr
          papply exists_intro i
          syntax_simp
          papply and_intro
          · pexact lt_ofNat hi
          · papply exists_intro (w ⟨i, Nat.lt_succ_of_lt hi⟩)
            papply exists_intro (w ⟨i + 1, Nat.succ_lt_succ hi⟩)
            simp_vec
            syntax_simp
            papply and_intro
            · have := hw ⟨i + 1, Nat.succ_lt_succ hi⟩
              simp only [Part.natrec_succ, Part.bind_eq_bind, Part.mem_bind_iff] at this
              rcases this with ⟨a, h, this⟩
              apply Part.mem_unique (hw ⟨i, Nat.lt_succ_of_lt hi⟩) at h
              subst h
              apply ih₂ at this
              simp_vec at this
              syntax_simp at this
              prw [this]
              prefl
            papply and_intro
            · prw [beta_ofNat]; rw [hi'']; prefl
            · rw [←ofNat_succ]; prw [nbeta_ofNat]; pexact ne_ofNat (Ne.symm hi')
  | mu f ih =>
    simp only [Partrec.mu_eval, Part.mem_find_iff, Part.pos_iff] at h
    rcases h with ⟨⟨a, h₁, h₁'⟩, h₂⟩
    cases a with
    | zero => simp at h₁'
    | succ a =>
      simp [rep_mu]
      papply iff_intro
      · prw [and_imp_iff]
        papply exists_elim'
        pintros
        syntax_simp
        prw [← double_neg_iff, ne_ofNat_iff, lt_ofNat_iff]
        papply or_elim'
        · papply orN_elim'
          intro ⟨k, hk⟩
          specialize h₂ k hk
          apply ih at h₂
          simp_vec at h₂
          syntax_simp at h₂
          pintro
          prw [0, h₂] at 2
          papply succ_ne_zero at 2
          passumption
        · pintro
          papply forall_elim m at 1
          syntax_simp
          papplya 1 at 0
          apply ih at h₁
          simp_vec at h₁
          syntax_simp at h₁
          prw [h₁, Proof.eq_comm] at 0
          papply succ_ne_zero at 0
          passumption
      · pintro
        papply and_intro
        · papply exists_intro a
          syntax_simp
          apply ih at h₁
          simp_vec at h₁
          syntax_simp at h₁
          prw [0, h₁]
          prefl
        · prw [0, bdall_ofNat_iff]
          apply andN_intro
          intro ⟨k, hk⟩
          syntax_simp
          specialize h₂ k hk
          apply ih at h₂
          simp_vec at h₂
          syntax_simp at h₂
          prw [h₂]
          prefl

theorem repPrim_iff {f : Primrec n} :
    ↑ᵀ^[k] Q ⊢ (repPrim f)[t ∷ᵥ Subst.of λ i => v i]ₚ ⇔ t ≐ f v := by
  prw [rep_iff_of_mem]
  · prefl
  · simp

theorem rep_of_mem {f : Partrec n} (h : m ∈ f v) :
    ↑ᵀ^[k] Q ⊢ (rep f)[m ∷ᵥ Subst.of λ i => v i]ₚ := by
  prw [rep_iff_of_mem h]; prefl

theorem neg_rep_of_not_mem {f : Partrec n} (hf : (f v).Dom) (h : m ∉ f v) :
    ↑ᵀ^[k] Q ⊢ ~ (rep f)[m ∷ᵥ Subst.of λ i => v i]ₚ := by
  prw [rep_iff_of_mem (Part.get_mem hf)]
  papply ne_ofNat
  simp only [ne_eq, Part.eq_get_iff_mem]
  exact h

theorem repRel_of_pos {f : Partrec n} :
    0 < f v → ↑ᵀ^[k] Q ⊢ (repRel f)[Subst.of λ i => v i]ₚ := by
  simp only [Part.pos_iff, forall_exists_index, and_imp]
  intro a h₁ h₂
  papply exists_intro (ofNat (a - 1))
  syntax_simp
  rw [← ofNat_succ, Nat.sub_add_cancel h₂]
  exact rep_of_mem h₁

theorem neg_repRel_of_zero {f : Partrec n} :
    0 ∈ f v → ↑ᵀ^[k] Q ⊢ ~ (repRel f)[Subst.of λ i => v i]ₚ := by
  intro h
  syntax_simp [repRel]
  papply exists_elim'
  pintros
  prw [rep_iff_of_mem h] at 0
  papply succ_ne_zero at 0
  passumption

end Q

open Q

namespace PA

theorem rep_prec_iff {f : Partrec k} {g : Partrec (k + 2)} :
    ↑ᵀ^[k + 2] PA ⊢ rep (f.prec g) ⇔ ∃' (
      ∃' ((rep f)[#0 ∷ᵥ Subst.shift 4]ₚ ⩑ beta #0 #1 0)
      ⩑ ∀[≺ #2] ∃' ∃' ((rep g)[#0 ∷ᵥ #2 ∷ᵥ #1 ∷ᵥ Subst.shift 6]ₚ ⩑ beta #1 #3 #2 ⩑ beta #0 #3 (S #2))
      ⩑ beta #1 #0 #2) := by
  simp only [rep_prec]
  papply iff_intro
  · papply exists_elim'
    pintro
    syntax_simp
    prw [and_imp_iff, and_imp_iff, and_imp_iff]
    pintros 4
    papply exists_intro #0
    syntax_simp
    papply and_intro
    · passumption
    papply and_intro <;> passumption
  · pintro
    papply exists_min at 0
    prevert
    papply Proof.exists_imp
    pintro
    syntax_simp
    prw [and_imp_iff, and_imp_iff, and_imp_iff]
    pintros 4
    papply and_intro
    · passumption
    papply and_intro
    · passumption
    papply and_intro
    · passumption
    pintros 2
    syntax_simp
    prw [← double_neg_iff, neg_or_iff, neg_exists_iff, Order.neg_bdex_iff]
    rw [← Formula.neg_eq (p := (∀' _) ⩑ _)]
    prw [and_imp_iff]
    pintros 2
    papply forall_elim #0 at 3
    syntax_simp
    pspecialize 3 with 1
    · passumption 2
    papplya 3
    pclear 3
    psuffices ∀[≺ S #3] ∀' (beta #0 #3 #1 ⇒ beta #0 #2 #1)
    · papply and_intro
      · prevert 6
        papply Proof.exists_imp
        pintro
        syntax_simp
        prw [and_imp_iff]
        pintros 2
        papply and_intro
        · passumption
        · papply forall_elim 0 at 2
          syntax_simp
          pspecialize 2
          · pexact zero_lt_succ
          papply forall_elim #0 at 2
          syntax_simp
          papplya 2
          passumption
      papply and_intro
      · pintros 2
        syntax_simp
        papply forall_elim #0 at 6
        syntax_simp
        pspecialize 6 with 1
        · passumption
        prevert 6
        papply Proof.exists_imp
        pintro
        papply Proof.exists_imp
        pintro
        syntax_simp
        prw [and_imp_iff, and_imp_iff]
        pintros 3
        papply and_intro
        · passumption
        papply and_intro
        · papply forall_elim #2 at 4
          syntax_simp
          pspecialize 4
          · papply lt_succ_of_lt; passumption
          papply forall_elim #1 at 4
          syntax_simp
          papplya 4
          passumption
        · papply forall_elim (S #2) at 4
          syntax_simp
          pspecialize 4
          · prw [succ_lt_succ_iff]; passumption
          papply forall_elim #0 at 4
          syntax_simp
          papplya 4
          passumption
      · papply forall_elim #3 at 0
        syntax_simp
        pspecialize 0
        · pexact lt_succ_self
        papply forall_elim #2 at 0
        syntax_simp
        papplya 0
        passumption
    · papply ind <;> syntax_simp
      · pintros 3
        syntax_simp
        pcontra
        prevert 8
        papply exists_elim'
        pintro
        prw [and_imp_iff]
        pintros 2
        papply forall_elim #0 at 6
        syntax_simp
        papplya 6
        papply and_intro
        · passumption
        · phave #0 ≐ #1
          · papply beta_unique <;> passumption
          · prw [0, nbeta_iff]
            passumption
      · pintros 5
        syntax_simp
        prw [succ_lt_succ_iff] at 1
        papply forall_elim #1 at 7
        syntax_simp
        pspecialize 7 with 1
        · passumption
        papply forall_elim #1 at 3
        syntax_simp
        pspecialize 3 with 1
        · passumption
        pspecialize 2 with 1
        · papply lt_succ_of_lt; passumption
        prevert 7
        papply exists_elim'
        pintro
        papply exists_elim'
        pintro
        prw [and_imp_iff, and_imp_iff]
        pintros 3
        syntax_simp
        pcontra
        papplya 7
        papply exists_intro #1
        papply exists_intro #0
        syntax_simp
        papply and_intro
        · passumption
        papply and_intro
        · papply forall_elim #1 at 6
          syntax_simp
          papplya 6
          passumption
        · phave #0 ≐ #2
          · papply beta_unique <;> passumption
          · prw [0, nbeta_iff]
            passumption

theorem rep_prec_iff' {f : Partrec n} {g : Partrec (n + 2)} :
    ↑ᵀ^[k] PA ⊢ (rep (f.prec g))[t₁ ∷ᵥ t₂ ∷ᵥ σ]ₚ ⇔ ∃'
      (∃' ((rep f)[#0 ∷ᵥ σ ∘ₛ Subst.shift 2]ₚ ⩑ beta (#0) (#1) 0) ⩑
        ∀[≺ ↑ₜt₂] ∃' ∃' ((rep g)[#0 ∷ᵥ #2 ∷ᵥ #1 ∷ᵥ σ ∘ₛ Subst.shift 4]ₚ ⩑ beta #1 #3 #2 ⩑ beta #0 #3 (S #2)) ⩑
          beta ↑ₜt₁ #0 ↑ₜt₂) := by
  have := Theory.iff_congr_subst (σ := t₁ ∷ᵥ t₂ ∷ᵥ σ) (rep_prec_iff (f := f) (g := g))
  syntax_simp at this
  exact this

theorem rep_prec_zero_iff {f : Partrec n} {g : Partrec (n + 2)} :
    ↑ᵀ^[k] PA ⊢ (rep (f.prec g))[t ∷ᵥ 0 ∷ᵥ σ]ₚ ⇔ (rep f)[t ∷ᵥ σ]ₚ := by
  prw [rep_prec_iff']
  syntax_simp
  papply iff_intro
  · papply exists_elim'
    pintro
    prw [and_imp_iff, and_imp_iff]
    pintros 3
    prevert 2
    papply exists_elim'
    pintro
    prw [and_imp_iff]
    pintros 2
    syntax_simp
    phave #0 ≐ ↑ₜ^[2] t
    · papply beta_unique <;> passumption
    prw [← 0]
    passumption
  · pintro
    papply exists_elim
    · papply beta_comprehension' 1 (#0 ≐ ↑ₜ^[2] t)
      pintros 2
      papply exists_intro ↑ₜt
      syntax_simp
      prefl
    pintros 2
    papply forall_elim 0 at 0
    syntax_simp
    pspecialize 0 with 1
    · pexact zero_lt_succ
    prevert
    papply exists_elim'
    pintro
    prw [and_imp_iff]
    pintros 2
    papply exists_intro #1
    syntax_simp
    papply and_intro
    · papply exists_intro #0
      syntax_simp
      papply and_intro
      · prw [1]; passumption
      · passumption
    papply and_intro
    · pintros 2
      syntax_simp
      papply not_lt_zero at 0
      papply false_elim
      passumption
    · prw [← 1]
      passumption

theorem rep_prec_succ_iff {f : Partrec n} {g : Partrec (n + 2)} :
    ↑ᵀ^[k] PA ⊢ (rep (f.prec g))[t₁ ∷ᵥ S t₂ ∷ᵥ σ]ₚ ⇔
      ∃' ((rep (f.prec g))[#0 ∷ᵥ ↑ₜt₂ ∷ᵥ σ ∘ₛ Subst.shift 1]ₚ
        ⩑ (rep g)[↑ₜt₁ ∷ᵥ ↑ₜt₂ ∷ᵥ #0 ∷ᵥ σ ∘ₛ Subst.shift 1]ₚ) := by
  prw [rep_prec_iff']
  syntax_simp
  papply iff_intro
  · papply exists_elim'
    pintro
    prw [and_imp_iff, and_imp_iff]
    papply exists_elim'
    pintro
    prw [and_imp_iff]
    pintros 4
    papply exists_elim
    · pexact beta_total #1 (↑ₜ^[2] t₂)
    pintros 2
    papply exists_intro #0
    syntax_simp
    papply and_intro
    · prw [rep_prec_iff']
      papply exists_intro #2
      syntax_simp
      papply and_intro
      · papply exists_intro #1
        syntax_simp
        papply and_intro <;> passumption
      papply and_intro
      · pintros 2
        papply forall_elim #0 at 3
        syntax_simp
        pspecialize 3 with 1
        · papply lt_succ_of_lt; passumption
        passumption
      · passumption
    · papply forall_elim (↑ₜ^[3] t₂) at 2
      syntax_simp
      pspecialize 2 with 1
      · pexact lt_succ_self
      prevert 2
      papply exists_elim'
      pintro
      papply exists_elim'
      pintro
      prw [and_imp_iff, and_imp_iff]
      pintros 3
      syntax_simp
      phave #0 ≐ ↑ₜ^[5] t₁
      · papply beta_unique <;> passumption
      phave #1 ≐ #2
      · papply beta_unique
        · passumption 2
        · passumption 4
      prw [← 1, ← 0]
      passumption
  · papply exists_elim'
    pintro
    prw [and_imp_iff, rep_prec_iff']
    papply exists_elim'
    pintro
    prw [and_imp_iff, and_imp_iff]
    pintros 4
    syntax_simp
    papply exists_elim
    · papply beta_comprehension' (S (S (↑ₜ^[2] t₂)))
        ((#1 ⪯ ↑ₜ^[4] t₂ ⇒ beta #0 #2 #1) ⩑ (#1 ≐ S (↑ₜ^[4] t₂) ⇒ #0 ≐ ↑ₜ^[4] t₁))
      pintro
      syntax_simp
      prw [lt_succ_iff_lt_or_eq, lt_succ_iff_lt_or_eq]
      papply or_elim'
      papply or_elim'
      · pintro
        papply forall_elim #0 at 3
        syntax_simp
        pspecialize 3 with 1
        · passumption
        prevert 3
        papply exists_elim'
        pintro
        papply exists_elim'
        pintro
        prw [and_imp_iff, and_imp_iff]
        pintros 3
        papply exists_intro #1
        syntax_simp
        papply and_intro
        · pintro; passumption
        · pintro
          prw [0] at 4
          papply PO.le_of_lt at 4
          papply succ_not_le_self at 4
          papply false_elim
          passumption
      · pintro
        papply exists_intro #2
        syntax_simp
        papply and_intro
        · pintro; prw [1]; passumption
        · pintro; prw [0] at 1; papply succ_ne_self at 1; papply false_elim; passumption
      · pintro
        papply exists_intro (↑ₜ^[3] t₁)
        syntax_simp
        papply and_intro
        · pintro; prw [1] at 0; papply succ_not_le_self at 0; papply false_elim; passumption
        · pintro; prefl
    · pintros 2
      papply exists_intro #0
      syntax_simp
      papply and_intro
      · prevert 4
        papply Proof.exists_imp
        pintro
        prw [and_imp_iff]
        pintros 2
        syntax_simp
        papply and_intro
        · passumption
        · papply forall_elim 0 at 2
          syntax_simp
          pspecialize 2 with 1
          · pexact zero_lt_succ
          prevert 2
          papply exists_elim'
          pintro
          syntax_simp
          prw [and_imp_iff, and_imp_iff]
          pintros 3
          pspecialize 2 with 1
          · pexact Q.zero_le
          phave #0 ≐ #1
          · papply beta_unique
            · passumption 2
            · passumption 3
          prw [← 0]
          passumption
      papply and_intro
      · pintro
        syntax_simp
        prw [lt_succ_iff_lt_or_eq]
        papply or_elim'
        · pintro
          papply forall_elim #0 at 4
          syntax_simp
          pspecialize 4 with 1
          · passumption
          prevert 4
          papply exists_elim'
          pintro
          papply exists_elim'
          pintro
          prw [and_imp_iff, and_imp_iff]
          pintros 3
          papply exists_intro #1
          papply exists_intro #0
          syntax_simp
          papply and_intro
          · passumption
          papply and_intro
          · papply forall_elim #2 at 4
            syntax_simp
            pspecialize 4 with 1
            · papply lt_succ_of_lt; papply lt_succ_of_lt; passumption
            prevert 4
            papply exists_elim'
            pintro
            syntax_simp
            prw [and_imp_iff, and_imp_iff]
            pintros 3
            pspecialize 2 with 1
            · papply PO.le_of_lt; passumption
            phave #0 ≐ #2
            · papply beta_unique
              · passumption 2
              · passumption 4
            prw [← 0]
            passumption
          · papply forall_elim (S #2) at 4
            syntax_simp
            pspecialize 4 with 1
            · prw [succ_lt_succ_iff]; papply lt_succ_of_lt; passumption
            prevert 4
            papply exists_elim'
            pintro
            syntax_simp
            prw [and_imp_iff, and_imp_iff]
            pintros 3
            pspecialize 2 with 1
            · prw [succ_le_iff_lt]; passumption
            phave #0 ≐ #1
            · papply beta_unique
              · passumption 2
              · passumption 3
            prw [← 0]
            passumption
        · pintro
          papply exists_intro #3
          papply exists_intro (↑ₜ^[4] t₁)
          syntax_simp
          papply and_intro
          · prw [0]; passumption
          papply and_intro
          · papply forall_elim (↑ₜ^[4] t₂) at 1
            syntax_simp
            pspecialize 1 with 1
            · papply lt_succ_of_lt; pexact lt_succ_self
            prevert 1
            papply exists_elim'
            pintro
            syntax_simp
            prw [and_imp_iff, and_imp_iff]
            pintros 3
            pspecialize 2 with 1
            · pexact PO.le_refl
            phave #0 ≐ #4
            · papply beta_unique
              · passumption 2
              · passumption 5
            prw [← 0, 4]
            passumption
          · papply forall_elim (S (↑ₜ^[4] t₂)) at 1
            syntax_simp
            pspecialize 1 with 1
            · pexact lt_succ_self
            prevert 1
            papply exists_elim'
            pintro
            syntax_simp
            prw [and_imp_iff, and_imp_iff]
            pintros 3
            pspecialize 1 with 1
            · prefl
            prw [← 1, 3]
            passumption
      · papply forall_elim (S (↑ₜ^[3] t₂)) at 0
        syntax_simp
        pspecialize 0 with 1
        · pexact lt_succ_self
        prevert 0
        papply exists_elim'
        pintro
        syntax_simp
        prw [and_imp_iff, and_imp_iff]
        pintros 3
        pspecialize 1 with 1
        · prefl
        prw [← 1]
        passumption

theorem rep_unique {f : Partrec n} :
    ↑ᵀ^[k] PA ⊢ (rep f)[t₁ ∷ᵥ σ]ₚ ⇒ (rep f)[t₂ ∷ᵥ σ]ₚ ⇒ t₁ ≐ t₂ := by
  induction f generalizing k with
  | const | succ | proj =>
    syntax_simp [rep_const, rep_succ, rep_proj]
    pintros
    prw [0, 1]
    prefl
  | comp f g ih₁ ih₂ =>
    syntax_simp [rep_comp]
    papply existsN_elim'
    apply forallN_intro
    prw [and_imp_iff]
    syntax_simp
    pintros 2
    papply existsN_elim'
    apply forallN_intro
    prw [and_imp_iff]
    pintros
    syntax_simp
    papply ih₁
    · passumption
    · papply eq_subst'
      · passumption
      · apply andN_intro
        intro i
        cases i using Fin.cases with syntax_simp
        | zero => prefl
        | succ i =>
          papply andN_elim i at 1
          papply andN_elim i at 3
          papply ih₂ i <;> passumption
  | prec f g ih₁ ih₂ =>
    psuffices ∀[≺ S (σ 0)] ∀' ∀' (
      (rep (f.prec g))[#1 ∷ᵥ #2 ∷ᵥ σ.tail ∘ₛ Subst.shift 3]ₚ
      ⇒ (rep (f.prec g))[#0 ∷ᵥ #2 ∷ᵥ σ.tail ∘ₛ Subst.shift 3]ₚ ⇒ #1 ≐ #0)
    · papply forall_elim (σ 0) at 0
      syntax_simp
      pspecialize 0 with 1
      · pexact lt_succ_self
      papply forall_elim t₁ at 0
      papply forall_elim t₂ at 0
      syntax_simp
      conv_rhs => rw [Vec.eq_cons σ]
      passumption 0
    papply ind <;> syntax_simp
    · pintros
      prw [rep_prec_zero_iff] at 1
      prw [rep_prec_zero_iff] at 0
      papply ih₁ <;> passumption
    · pintros
      syntax_simp
      prw [succ_lt_succ_iff] at 2
      pspecialize 3 with 1
      · papply lt_succ_of_lt; passumption
      prw [rep_prec_succ_iff] at 1
      prevert 1
      papply exists_elim'
      pintro
      prw [and_imp_iff]
      pintros
      syntax_simp
      prw [rep_prec_succ_iff] at 2
      prevert 2
      papply exists_elim'
      pintro
      prw [and_imp_iff]
      pintros
      syntax_simp
      papply forall_elim #1 at 5
      papply forall_elim #0 at 5
      syntax_simp
      pspecialize 5
      · passumption
      · passumption
      papply ih₂
      · passumption
      · prw [5]; passumption
  | mu f ih =>
    syntax_simp [rep_mu]
    prw [and_imp_iff]
    papply exists_elim'
    pintros 3
    syntax_simp
    prw [and_imp_iff]
    papply exists_elim'
    pintro
    syntax_simp
    pintros
    prw [← double_neg_iff, LO.ne_iff_lt_or_gt]
    papply or_elim'
    · pintro
      papply forall_elim (↑ₜ^[2] t₁) at 1
      syntax_simp
      papplya 1 at 0
      papply succ_ne_zero (t := #1)
      papply ih <;> passumption
    · pintro
      papply forall_elim (↑ₜ^[2] t₂) at 3
      syntax_simp
      papplya 3 at 0
      papply succ_ne_zero (t := #0)
      papply ih <;> passumption

theorem repPrim_total {f : Primrec n} (σ) : ↑ᵀ^[k] PA ⊢ ∃' (repPrim f)[⇑ₛσ]ₚ := by
  induction f generalizing k with
  | const m =>
    simp only [repPrim, Partrec.ofPrim, rep_const]
    papply exists_intro m
    syntax_simp
    prefl
  | succ =>
    simp only [repPrim, Partrec.ofPrim, rep_succ]
    papply exists_intro (S (σ 0))
    syntax_simp
    prefl
  | proj i =>
    simp only [repPrim, Partrec.ofPrim, rep_proj]
    papply exists_intro (σ i)
    syntax_simp
    prefl
  | @comp n m f g ih₁ ih₂ =>
    syntax_simp [repPrim, Partrec.ofPrim, rep_comp]
    papply existsN_elim
    · papply existsN_andN_of_andN_exists
      apply andN_intro
      intro i
      pexact ih₂ i σ
    apply forallN_intro
    pintro
    syntax_simp
    papply exists_elim
    · pexact ih₁ (Subst.embed n)
    pintros 2
    papply exists_intro #0
    syntax_simp
    papply existsN_intro (Subst.embed n ∘ₛ Subst.shift 1)
    syntax_simp
    papply and_intro <;> passumption
  | prec f g ih₁ ih₂ =>
    syntax_simp [repPrim, Partrec.ofPrim]
    psuffices ∀[≺ S (σ 0)] ∃' (rep ((Partrec.ofPrim f).prec (Partrec.ofPrim g)))[#0 ∷ᵥ #1 ∷ᵥ σ.tail ∘ₛ Subst.shift 2]ₚ
    · papply forall_elim (σ 0) at 0
      conv_rhs => rw [Vec.eq_cons σ]
      syntax_simp [Vec.head]
      pspecialize 0 with 1
      · pexact lt_succ_self
      passumption
    papply ind <;> syntax_simp
    · pintro
      papply exists_elim
      · pexact ih₁ σ.tail
      pintros 2
      papply exists_intro #0
      syntax_simp
      prw [rep_prec_zero_iff]
      passumption
    · pintros 3
      prw [succ_lt_succ_iff] at 0
      pspecialize 1 with 1
      · papply lt_succ_of_lt; passumption
      prevert 1
      papply exists_elim'
      pintros 2
      papply exists_elim
      · pexact ih₂ (#1 ∷ᵥ #0 ∷ᵥ σ.tail ∘ₛ Subst.shift 2)
      pintros 2
      papply exists_intro #0
      syntax_simp
      prw [rep_prec_succ_iff]
      papply exists_intro #1
      syntax_simp
      papply and_intro <;> passumption

end Theory.PA

namespace peano

instance : Encodable (peano.Func n) where
  encode
  | .zero => 0
  | .succ => 0
  | .add => 0
  | .mul => 1
  decode m :=
    match n, m with
    | 0, 0 => some .zero
    | 1, 0 => some .succ
    | 2, 0 => some .add
    | 2, 1 => some .mul
    | _, _ => none
  encodek f := by cases f <;> rfl

instance : Encodable (peano.Rel n) := inferInstanceAs (Encodable Empty)

open Primrec

instance : peano.PrimCodable where
  isFuncPR := orv [
    and (eq (proj 0) zero) (eq (proj 1) zero),
    and (eq (proj 0) (const 1)) (eq (proj 1) zero),
    and (eq (proj 0) (const 2)) (eq (proj 1) zero),
    and (eq (proj 0) (const 2)) (eq (proj 1) (const 1))
  ]ᵥ
  isFuncPR_eval_pos_iff := by
    intros; simp
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exists .zero
      · exists .succ
      · exists .add
      · exists .mul
    · intro ⟨f, h⟩; cases f <;> subst h <;> simp <;> rfl
  isRelPR := zero
  isRelPR_eval_pos_iff := by have : ∀ n, IsEmpty (peano.Rel n) := λ _ => Empty.instIsEmpty; simp

instance : peano.HasConstEncodeZero := ⟨.zero, rfl⟩

def zeroPR : Primrec 0 :=
  Term.funcPR.comp₃ zero zero zero
theorem zeroPR_eval (n) : zeroPR []ᵥ = Encodable.encode (0 : peano.Term n) := by
  simp [zeroPR, ←zero_eq]; convert Term.funcPR_eval; rfl

def succPR : Primrec 1 :=
  Term.funcPR.comp₃ (const 1) zero (Primrec.pair.comp₂ (proj 1) zero)
theorem succPR_eval {t : peano.Term n} : succPR [Encodable.encode t]ᵥ = Encodable.encode (S t) := by
  simp [succPR, ←succ_eq]; convert Term.funcPR_eval <;> rfl

def ofNatPR : Primrec 1 :=
  zeroPR.prec (succPR.comp₁ (proj 1))
theorem ofNatPR_eval (n) : ofNatPR [m]ᵥ = Encodable.encode (ofNat m : peano.Term n) := by
  simp [ofNatPR]
  induction m with
  | zero => simp [prec_eval_zero, zeroPR_eval n, ofNat_zero]
  | succ m ih => simp [prec_eval_succ, ih, succPR_eval, ofNat_succ]

end peano

open peano

namespace Theory.Q

variable [Encodable α] {s : Set α} {T : peano.Theory} [Recursive T] [Q ⊆ᵀ T]

/--
  In an ω-consistent recursive theory `T` extending `Q`, a set is weakly representable in `T` iff it
  is enumerable. The ω-consistency condition can be weakened to consistency using Rosser's trick.
  -/
theorem enumerable_iff_weakly_representable (h : OmegaConsistent T) :
  IsEnumerable s ↔ ∃ (p : peano.Formula 1), ∀ x, x ∈ s ↔ T ⊢ p[[⌜x⌝]ᵥ]ₚ := by
  classical
  constructor
  · intro ⟨_⟩
    exists ∃' (repRel (Enumerable.enum s))
    intro x
    constructor
    · rw [Enumerable.mem_iff]; intro ⟨n, h₁⟩
      papply Proof.exists_intro n
      syntax_simp
      apply repRel_of_pos at h₁
      simp_vec at h₁
      pexact h₁
    · intro h₁
      by_contra h₂; rw [Enumerable.not_mem_iff] at h₂
      refine h _ ⟨h₁, ?_⟩
      intro n
      specialize h₂ n
      apply neg_repRel_of_zero at h₂
      simp_vec at h₂
      syntax_simp
      pexact h₂
  · intro ⟨p, h₁⟩
    refine ⟨⟨(isProofPR T).comp₂ (.proj 0)
      (.ofPrim (Formula.substSinglePR.comp₃ .zero (.const (Encodable.encode p)) (ofNatPR.comp₁ (.proj 1)))), ?_, ?_⟩⟩
    · intro n x
      simp [ofNatPR_eval 0, Formula.substSinglePR_eval]
      exact isProofPR_dom
    · intro x
      simp [ofNatPR_eval 0, Formula.substSinglePR_eval, ←provable_iff_isProofPR_eval_pos]; simp [Vec.eq_one]
      exact h₁ x

/-- In a consistent theory `T` extending `Q`, a set is strongly representable in `T` iff it is recursive. -/
theorem recursive_iff_strongly_representable (h : Consistent T) :
  IsRecursive s ↔ ∃ (p : peano.Formula 1), (∀ x ∈ s, T ⊢ p[[⌜x⌝]ᵥ]ₚ) ∧ (∀ x ∉ s, T ⊢ ~ p[[⌜x⌝]ᵥ]ₚ) := by
  constructor
  · intro ⟨_⟩
    exists repRel (Recursive.char s)
    constructor
    · intro x h₁; rw [Recursive.mem_iff] at h₁
      apply repRel_of_pos at h₁; simp_vec at h₁
      pexact h₁
    · intro x h₁; rw [Recursive.not_mem_iff] at h₁
      apply neg_repRel_of_zero at h₁; simp_vec at h₁
      pexact h₁
  · intro ⟨p, h₁, h₂⟩
    rw [IsRecursive.iff_re_compl_re]
    constructor
    · refine ⟨⟨(isProofPR T).comp₂ (.proj 0) (.ofPrim
        (Formula.substSinglePR.comp₃ .zero (.const (Encodable.encode p)) (ofNatPR.comp₁ (.proj 1)))), ?_, ?_⟩⟩
      · intro n x
        simp [ofNatPR_eval 0, Formula.substSinglePR_eval]
        exact isProofPR_dom
      · intro x
        simp [ofNatPR_eval 0, Formula.substSinglePR_eval, ←provable_iff_isProofPR_eval_pos]; simp [Vec.eq_one]
        by_cases h₃ : x ∈ s <;> simp [h₃]
        · exact h₁ x h₃
        · apply h.unprovable_of_disprovable; exact h₂ x h₃
    · refine ⟨⟨(isProofPR T).comp₂ (.proj 0) (.ofPrim (Formula.negPR.comp₁
        (Formula.substSinglePR.comp₃ .zero (.const (Encodable.encode p)) (ofNatPR.comp₁ (.proj 1))))), ?_, ?_⟩⟩
      · intro n x
        simp [ofNatPR_eval 0, Formula.substSinglePR_eval]
        exact isProofPR_dom
      · intro x
        simp [ofNatPR_eval 0, Formula.substSinglePR_eval, ←provable_iff_isProofPR_eval_pos]; simp [Vec.eq_one]
        by_cases h₃ : x ∈ s <;> simp [h₃]
        · apply h.undisprovable_of_provable; exact h₁ x h₃
        · exact h₂ x h₃
end Q

open Primrec

instance : Recursive Q where
  char := .ofPrim (orv [
    eq (proj 0) (const (Encodable.encode (∀' (~ S #0 ≐ 0) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' ∀' ((S #1 ≐ S #0) ⇒ #1 ≐ #0) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' (#0 + 0 ≐ #0) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' ∀' (#1 + S #0 ≐ S (#1 + #0)) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' (#0 * 0 ≐ 0) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' ∀' (#1 * S #0 ≐ #1 * #0 + #1) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' (#0 ≐ 0 ⩒ ∃' (#1 ≐ S #0)) : peano.Sentence)))
  ]ᵥ)
  char_dom := by simp
  mem_iff p := by
    simp [Fin.exists_fin_succ]
    constructor
    · intro h; cases h <;> simp
    · intro h
      repeat' on_goal 1 => rcases h with rfl | h; constructor

instance : Recursive PA where
  char := .ofPrim (orv [
    eq (proj 0) (const (Encodable.encode (∀' (~ S #0 ≐ 0) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' ∀' ((S #1 ≐ S #0) ⇒ #1 ≐ #0) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' (#0 + 0 ≐ #0) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' ∀' (#1 + S #0 ≐ S (#1 + #0)) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' (#0 * 0 ≐ 0) : peano.Sentence))),
    eq (proj 0) (const (Encodable.encode (∀' ∀' (#1 * S #0 ≐ #1 * #0 + #1) : peano.Sentence))),
    bdExists (succ.comp₁ (proj 0)) (bdExists (proj 1) (andv [
      peano.isFormulaPR.comp₂ (succ.comp₁ (proj 1)) (proj 0),
      eq (proj 2) (Formula.allsPR.comp₂ (proj 1) (Formula.impPR.comp₂
        (Formula.substSinglePR.comp₃ (proj 1) (proj 0) zeroPR.comp₀)
        (Formula.impPR.comp₂
          (Formula.allPR.comp₁ (Formula.impPR.comp₂ (proj 0) (Formula.substAssignPR.comp₃ (proj 1) (proj 0) (succPR.comp₁ (Term.varPR.comp₁ zero)))))
          (Formula.allPR.comp₁ (proj 0)))))
    ]ᵥ))
  ]ᵥ)
  char_dom := by simp
  mem_iff p := by
    simp [Fin.exists_fin_succ]
    constructor
    · intro h
      cases h with
      | @ax_ind n p =>
        repeat right
        refine ⟨n, ?_, Encodable.encode p, ?_, ?_, ?_⟩
        · simp [Nat.lt_succ]; exact Formula.encode_le_alls_n
        · apply Formula.encode_le_alls_p.trans_lt'
          apply Formula.encode_lt_imp_right.trans'
          apply Formula.encode_lt_imp_right.trans'
          exact Formula.encode_lt_all
        · simp [isFormulaPR_eval_pos_iff]
        · simp [zeroPR_eval n, Term.varPR_eval (L := peano) (Nat.zero_lt_succ n), succPR_eval,
            Formula.substSinglePR_eval, Formula.substAssignPR_eval]
      | _ => simp
    · intro h
      repeat' on_goal 1 => rcases h with rfl | h; constructor
      rcases h with ⟨n, _, _, _, h₁, h₂⟩
      simp [isFormulaPR_eval_pos_iff] at h₁
      rcases h₁ with ⟨p, rfl⟩
      simp [zeroPR_eval n, Term.varPR_eval (L := peano) (Nat.zero_lt_succ n), succPR_eval,
        Formula.substSinglePR_eval, Formula.substAssignPR_eval] at h₂
      subst h₂
      constructor

end FirstOrder.Language.Theory
