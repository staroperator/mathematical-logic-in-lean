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
    (⋀ i, (rep (g i))[#(i.castAdd' (n + 1)) ∷ᵥ λ j => #(j.succ.addNat k)]ₚ)
    ⩑ (rep f)[#(Fin.addNat 0 k) ∷ᵥ λ i => #(i.castAdd' (n + 1))]ₚ)
| .prec f g =>
  ∃' (
    ∃' ((rep f)[#0 ∷ᵥ λ i => #(i.addNat 4)]ₚ ⩑ beta #0 #1 0)
    ⩑ ∀[≺ #2] ∃' ∃' ((rep g)[#0 ∷ᵥ #2 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 6)]ₚ ⩑ beta #1 #3 #2 ⩑ beta #0 #3 (S #2))
    ⩑ beta #1 #0 #2
    -- to make `rep` weakly representable in `Q`, we have to add this annoying minimization condition
    ⩑ ∀[≺ #0] (
      ∃' ((rep f)[#0 ∷ᵥ λ i => #(i.addNat 5)]ₚ ⩑ nbeta #0 #1 0)
      ⩒ ∃[≺ #3] ∃' ∃' ((rep g)[#0 ∷ᵥ #2 ∷ᵥ #1 ∷ᵥ λ i => #(i.addNat 7)]ₚ ⩑ beta #1 #3 #2 ⩑ nbeta #0 #3 (S #2))))
| .mu f =>
  (∃' ((rep f)[≔ₛ S #0]ₚ)) ⩑ ∀[≺ #0] (rep f)[0 ∷ᵥ #0 ∷ᵥ λ i => #(i.addNat 2)]ₚ

abbrev repPrim (f : Primrec n) := rep (.ofPrim f)

theorem Sigma₁.rep : Sigma₁ (rep f) := by
  induction f <;> with_unfolding_all simp [peano.rep]; aesop

def repRel (f : Partrec n) : peano.Formula n :=
  ∃' ((rep f)[≔ₛ S #0]ₚ)

theorem Sigma₁.repRel : Sigma₁ (repRel f) := ex (subst rep)

end peano

theorem Proof.existsN_andN_of_andN_exists {L : Language} {Γ : L.FormulaSet n} {v : Vec (L.Formula (n + 1)) m} :
  Γ ⊢ (⋀ i, ∃' v i) ⇒ ∃^[m] (⋀ i, (v i)[#(i.castAdd' n) ∷ᵥ λ j => #(j.addNat m)]ₚ) := by
  induction m with simp [Formula.exN, Formula.andN, Vec.head, Vec.tail, Function.comp]
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
      simp [Formula.shiftN_eq_subst, Formula.subst_exN, Formula.subst_andN, ←Formula.subst_comp, Subst.comp_def]
      papply existsN_intro λ i => #(i.castAdd' n)
      papply exists_elim
      · papply and_left at 1
        passumption 1
      · pintros 2
        papply exists_intro #0
        simp [Formula.shift, Formula.subst_andN, ←Formula.subst_comp, Subst.comp_def, Subst.lift]
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
  ↑ᵀ^[k] Q ⊢ (rep f)[t ∷ᵥ λ i => v i]ₚ ⇔ t ≐ m := by
  classical
  induction f generalizing k m t with (simp [rep]; try simp at h)
  | const m => simp [h]; prefl
  | succ => simp [h, Vec.head]; prefl
  | proj i => simp [h]; prefl
  | comp f g ih₁ ih₂ =>
    rcases h with ⟨u, h₁, h₂⟩
    simp [Formula.subst_exN, Formula.subst_andN, ←Formula.subst_comp, Subst.comp_def]
    papply iff_intro
    · papply existsN_elim'
      apply forallN_intro; simp
      prw [and_imp_iff]; pintros
      prw [←ih₁ h₂]
      papply eq_subst'
      · passumption
      · apply andN_intro
        intro i
        cases i using Fin.cases with simp
        | zero => prefl
        | succ i =>
          papply andN_elim i at 1
          prw [←ih₂ i (h₁ i)]
          passumption
    · pintro
      papply existsN_intro λ i => u i
      simp [Formula.subst_andN, ←Formula.subst_comp, Subst.comp_def]
      papply and_intro
      · apply andN_intro
        intro i
        prw [ih₂ i (h₁ i)]
        prefl
      · simp [Term.shiftN_eq_subst, ←Term.subst_comp, Subst.comp_def]; rw [←Subst.id_def, Term.subst_id]
        prw [ih₁ h₂]
        passumption
  | prec f g ih₁ ih₂ =>
    simp [Partrec.prec_eval] at h
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
    simp [←Formula.subst_comp, Subst.comp_def, Subst.lift]
    papply iff_intro
    · papply exists_elim'
      pintro; simp; prw [and_imp_iff, and_imp_iff, and_imp_iff]; pintros
      psuffices #0 ≐ a
      · prw [0, beta_ofNat] at 2; prw [2]
        rw [ha l (Nat.lt_succ_self _), h]
        prefl
      · prw [←double_neg_iff, ne_ofNat_iff, lt_ofNat_iff]
        papply or_elim'
        · papply orN_elim'
          intro ⟨b, hb⟩; apply Nat.find_min at hb; simp at hb
          pintro
          cases hb' : Nat.find hb with
          | zero =>
            simp at hb'
            papply exists_elim
            · passumption 4
            · pintro; prw [and_imp_iff]; pintros; simp [←ofNat_zero]
              prw [ih₁ (hw 0)] at 1
              prw [1, 2, beta_ofNat] at 0
              papply ne_ofNat (Ne.symm hb') at 0
              passumption
          | succ i =>
            simp [Nat.find_eq_iff] at hb'
            rcases hb' with ⟨⟨hi, hi'⟩, hi''⟩
            specialize hi'' i (Nat.lt_succ_self _) (Nat.lt_succ_of_lt hi)
            papply forall_elim i at 3; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift]
            papply exists_elim
            · papplya 3; pexact lt_ofNat hi
            · pintro; simp
              papply exists_elim'
              pintro; prw [and_imp_iff, and_imp_iff]; pintros; simp [←ofNat_succ]
              prw [3, beta_ofNat] at 1; rw [hi'']
              have := hw ⟨i + 1, Nat.succ_lt_succ hi⟩; simp [Part.natrec_succ] at this
              rcases this with ⟨_, h, this⟩
              apply Part.mem_unique (hw ⟨i, Nat.lt_succ_of_lt hi⟩) at h; subst h
              apply ih₂ at this; simp_vec at this
              prw [1, this] at 2
              prw [2, 3, beta_ofNat] at 0
              papply ne_ofNat (Ne.symm hi') at 0
              passumption
        · pintro
          papply forall_elim a at 1; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift]
          papplya 1 at 0; pclear 1
          prw [bdex_ofNat_iff] at 0; simp [Subst.lift, Subst.single]
          prevert
          papply or_elim'
          · papply exists_elim'
            pintro; prw [and_imp_iff]; pintros; simp [←ofNat_zero]
            prw [ih₁ (hw 0)] at 1
            prw [1, nbeta_ofNat] at 0
            papplya 0; rw [ha 0 (Nat.zero_lt_succ _)]
            prefl
          · papply orN_elim'
            intro ⟨i, hi⟩; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift]
            papply exists_elim'
            pintro
            papply exists_elim'
            pintro; prw [and_imp_iff, and_imp_iff]; pintros; simp [←ofNat_succ]
            prw [beta_ofNat] at 1; rw [ha i (Nat.lt_succ_of_lt hi)]
            have := hw ⟨i + 1, Nat.succ_lt_succ hi⟩; simp [Part.natrec_succ] at this
            rcases this with ⟨_, h, this⟩
            apply Part.mem_unique (hw ⟨i, Nat.lt_succ_of_lt hi⟩) at h; subst h
            apply ih₂ at this; simp_vec at this
            prw [1, this] at 2
            prw [2, nbeta_ofNat] at 0
            papplya 0; rw [ha (i + 1) (Nat.succ_lt_succ hi)]
            prefl
    · pintro
      papply exists_intro a; simp [←Formula.subst_comp, Subst.comp_def, Subst.lift, Term.shift_subst_single]
      papply and_intro
      · papply exists_intro (w 0); simp [←Formula.subst_comp, Subst.comp_def]
        papply and_intro
        · prw [ih₁ (hw 0)]; prefl
        · rw [←ofNat_zero]; prw [beta_ofNat]; rw [ha 0 (Nat.zero_lt_succ _)]; prefl
      papply and_intro
      · prw [bdall_ofNat_iff]
        apply andN_intro
        intro ⟨i, hi⟩; simp
        papply exists_intro (w ⟨i, Nat.lt_succ_of_lt hi⟩)
        papply exists_intro (w ⟨i + 1, Nat.succ_lt_succ hi⟩)
        simp [←Formula.subst_comp, Subst.comp_def]
        papply and_intro
        · have := hw ⟨i + 1, Nat.succ_lt_succ hi⟩; simp [Part.natrec_succ] at this
          rcases this with ⟨a, h, this⟩
          apply Part.mem_unique (hw ⟨i, Nat.lt_succ_of_lt hi⟩) at h; subst h
          apply ih₂ at this; simp_vec at this
          prw [this]; prefl
        papply and_intro
        · prw [beta_ofNat]; rw [ha i (Nat.lt_succ_of_lt hi)]; prefl
        · rw [←ofNat_succ]; prw [beta_ofNat]; rw [ha (i + 1) (Nat.succ_lt_succ hi)]; prefl
      papply and_intro
      · prw [0, beta_ofNat]; rw [ha l (Nat.lt_succ_self _), h]; prefl
      · prw [bdall_ofNat_iff]
        apply andN_intro
        intro ⟨b, hb⟩
        apply Nat.find_min at hb; simp at hb
        cases hb' : Nat.find hb with simp [←Formula.subst_comp, Subst.comp_def, Subst.lift]
        | zero =>
          simp at hb'
          papply or_inl
          papply exists_intro (w 0); simp [←Formula.subst_comp, Subst.comp_def]
          papply and_intro
          · prw [ih₁ (hw 0)]; prefl
          · rw [←ofNat_zero]; prw [nbeta_ofNat]; pexact ne_ofNat (Ne.symm hb')
        | succ i =>
          simp [Nat.find_eq_iff] at hb'
          rcases hb' with ⟨⟨hi, hi'⟩, hi''⟩
          specialize hi'' i (Nat.lt_succ_self _) (Nat.lt_succ_of_lt hi)
          papply or_inr
          papply exists_intro i; simp [←Formula.subst_comp, Subst.comp_def]
          papply and_intro
          · pexact lt_ofNat hi
          · papply exists_intro (w ⟨i, Nat.lt_succ_of_lt hi⟩)
            papply exists_intro (w ⟨i + 1, Nat.succ_lt_succ hi⟩)
            simp [←Formula.subst_comp, Subst.comp_def]
            papply and_intro
            · have := hw ⟨i + 1, Nat.succ_lt_succ hi⟩; simp [Part.natrec_succ] at this
              rcases this with ⟨a, h, this⟩
              apply Part.mem_unique (hw ⟨i, Nat.lt_succ_of_lt hi⟩) at h; subst h
              apply ih₂ at this; simp_vec at this
              prw [this]; prefl
            papply and_intro
            · prw [beta_ofNat]; rw [hi'']; prefl
            · rw [←ofNat_succ]; prw [nbeta_ofNat]; pexact ne_ofNat (Ne.symm hi')
  | mu f ih =>
    simp [Part.mem_find_iff, Part.pos_iff] at h; rcases h with ⟨⟨a, h₁, h₁'⟩, h₂⟩
    cases' a with a <;> simp at h₁'
    papply iff_intro
    · prw [and_imp_iff]
      papply exists_elim'
      pintros
      simp [←Formula.subst_comp, Subst.comp_def]; simp_vec; rw [←Term.shift]
      prw [←double_neg_iff, ne_ofNat_iff, lt_ofNat_iff]
      papply or_elim'
      · papply orN_elim'
        intro ⟨k, hk⟩
        specialize h₂ k hk; apply ih at h₂; simp_vec at h₂
        pintro
        prw [0, h₂] at 2
        papply succ_ne_zero at 2
        passumption
      · pintro
        papply forall_elim m at 1
        simp [←Term.subst_comp, ←Formula.subst_comp]; simp [Term.shift_subst_single, Subst.comp_def]
        papplya 1 at 0
        apply ih at h₁; simp_vec at h₁
        prw [h₁, Proof.eq_comm] at 0
        papply succ_ne_zero at 0
        passumption
    · pintro
      papply and_intro
      · papply exists_intro a
        simp [←Formula.subst_comp, Subst.comp_def]; simp_vec; simp [Term.shift_subst_single]
        apply ih at h₁; simp_vec at h₁
        prw [0, h₁]
        prefl
      · prw [0, bdall_ofNat_iff]
        apply andN_intro
        intro ⟨k, hk⟩
        specialize h₂ k hk; apply ih at h₂; simp_vec at h₂
        simp [←Formula.subst_comp]; simp [Subst.comp_def]
        prw [h₂]
        prefl

theorem repPrim_iff {f : Primrec n} :
  ↑ᵀ^[k] Q ⊢ (repPrim f)[t ∷ᵥ λ i => v i]ₚ ⇔ t ≐ f v := by
  simp [repPrim]
  prw [rep_iff_of_mem]
  · prefl
  · simp

theorem rep_of_mem {f : Partrec n} (h : m ∈ f v) :
  ↑ᵀ^[k] Q ⊢ (rep f)[m ∷ᵥ λ i => v i]ₚ := by
  prw [rep_iff_of_mem h]; prefl

theorem neg_rep_of_not_mem {f : Partrec n} (hf : (f v).Dom) (h : m ∉ f v) :
  ↑ᵀ^[k] Q ⊢ ~ (rep f)[m ∷ᵥ λ i => v i]ₚ := by
  prw [rep_iff_of_mem (Part.get_mem hf)]
  papply ne_ofNat
  simp [Part.eq_get_iff_mem]
  exact h

theorem repRel_of_pos {f : Partrec n} :
  0 < f v → ↑ᵀ^[k] Q ⊢ (repRel f)[λ i => v i]ₚ := by
  simp [Part.pos_iff]
  intro a h₁ h₂
  papply exists_intro (ofNat (a - 1))
  simp [repRel, ←Formula.subst_comp, Subst.comp_def]; simp_vec
  rw [←ofNat_succ, Nat.sub_add_cancel h₂]
  exact rep_of_mem h₁

theorem neg_repRel_of_zero {f : Partrec n} :
  0 ∈ f v → ↑ᵀ^[k] Q ⊢ ~ (repRel f)[λ i => v i]ₚ := by
  intro h
  simp [repRel, ←Formula.subst_comp, Subst.comp_def]; simp_vec
  papply exists_elim'
  pintros
  prw [rep_iff_of_mem h] at 0
  papply succ_ne_zero at 0
  passumption

end Q

open Q

namespace PA

theorem rep_unique {f : Partrec n} : ↑ᵀ^[k] PA ⊢ (rep f)[t₁ ∷ᵥ σ]ₚ ⇒ (rep f)[t₂ ∷ᵥ σ]ₚ ⇒ t₁ ≐ t₂ := by
  induction f generalizing k with simp [rep]
  | const | succ | proj => pintros; prw [0, 1]; prefl
  | comp f g ih₁ ih₂ =>
    simp [Formula.subst_exN, Formula.subst_andN, ←Formula.subst_comp, Subst.comp_def]
    papply existsN_elim'
    apply forallN_intro; simp
    prw [and_imp_iff]; pintros
    simp [Formula.shiftN_eq_subst, Formula.subst_exN, Formula.subst_andN, ←Formula.subst_comp, Subst.comp_def]
    papply existsN_elim'
    apply forallN_intro; simp
    prw [and_imp_iff]; pintros
    simp [Term.shiftN_eq_subst, Formula.shiftN_eq_subst, Formula.subst_andN, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def]
    papply ih₁
    · passumption
    · papply eq_subst'
      · passumption
      · apply andN_intro
        intro i
        cases i using Fin.cases with simp
        | zero => prefl
        | succ i =>
          papply andN_elim i at 1
          papply andN_elim i at 3
          papply ih₂ i <;> passumption
  | prec f g ih₁ ih₂ =>
    simp [←Formula.subst_comp, Subst.comp_def, Subst.lift]
    papply exists_elim'
    pintro
    prw [and_imp_iff, and_imp_iff, and_imp_iff]; pintros 4; pclear 0
    papply exists_elim'
    pintro; simp [Term.shift_subst_lift, ←Formula.subst_comp, Subst.comp_def, Subst.lift, ←Term.shift_def]
    prw [and_imp_iff, and_imp_iff, and_imp_iff]; pintros 4; pclear 0
    simp_vec; simp [Term.shift_subst_cons]
    psuffices ∀[≺ S ↑ₜ↑ₜ(σ 0)] ∀' ∀' (beta #1 #4 #2 ⇒ beta #0 #3 #2 ⇒ #1 ≐ #0)
    · papply forall_elim ↑ₜ↑ₜ(σ 0) at 0; simp [Term.shift_subst_single, Subst.lift]; simp [Subst.single]
      phave ↑ₜ↑ₜ(σ 0) ≺ S ↑ₜ↑ₜ(σ 0)
      · pexact lt_succ_self
      · papplya 1 at 0
        papply forall_elim ↑ₜ↑ₜt₁ at 0; simp [Term.shift_subst_lift, Term.shift_subst_single]; simp [Subst.lift, Subst.single]
        papply forall_elim ↑ₜ↑ₜt₂ at 0; simp [Term.shift_subst_single]; simp [Subst.single]
        papplya 0
        · passumption
        · conv => arg 2; simp [Term.shift, ←Term.subst_comp, Subst.comp_def]
          passumption
    · papply ind <;> simp [Term.shift_subst_single, Term.shift_subst_assign] <;> simp [Subst.lift, Subst.single, Subst.assign]
      · pintro; pclear 0
        pintros; simp
        papply exists_elim
        · passumption 7
        pintro; simp [←Formula.subst_comp, Subst.comp_def]; simp [Term.shift_subst_lift]
        prw [and_imp_iff]; pintros 2
        papply exists_elim
        · passumption 6
        pintro; simp [←Formula.subst_comp, Subst.comp_def]; simp [Term.shift_subst_cons, Subst.lift]
        simp_vec; simp [Term.shift_subst_cons, ←Term.subst_comp, Subst.comp_def]
        simp [Formula.shift, Term.shift, ←Formula.subst_comp, ←Term.subst_comp, Subst.comp_def]
        prw [and_imp_iff]; pintros
        papply beta_unique at 0 with 2; swap
        · passumption 4
        papply beta_unique at 2 with 2; swap
        · passumption 5
        prw [0, 2]
        papply ih₁ <;> passumption
      · pintros; simp
        prw [succ_lt_succ_iff] at 2
        papply forall_elim #2 at 8; simp [Term.shift_subst_lift, Term.shift_subst_single]
        papply exists_elim
        · papplya 8
          passumption 2
        pintro
        papply exists_elim'
        pintro; simp [←Formula.subst_comp, Subst.comp_def]; simp [Term.shift_subst_lift, Term.shift_subst_single]; simp [Subst.lift, Subst.single]
        prw [and_imp_iff, and_imp_iff]
        pintros
        papply forall_elim #4 at 8; simp [Term.shift_subst_lift, Term.shift_subst_single]
        papply exists_elim
        · papplya 8
          simp [Term.shift, ←Term.subst_comp, Subst.comp_def]
          passumption 5
        pintro
        papply exists_elim'
        pintro; simp [←Formula.subst_comp, ←Term.subst_comp, Subst.comp_def]; simp [Subst.lift, Subst.single]
        prw [and_imp_iff, and_imp_iff]; pintros
        papply lt_succ_of_lt at 8
        papplya 9 at 8
        papply forall_elim #3 at 8
        papply forall_elim #1 at 8
        simp [Subst.lift, Subst.single]
        papplya 8 at 4
        papplya 4 at 1
        simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def]
        prw [←1] at 2
        papply ih₂ at 2 with 2; swap
        · passumption 5
        papply beta_unique at 3 with 2; swap
        · passumption 7
        papply beta_unique at 0 with 2; swap
        · passumption 6
        prw [0, 3, 2]
        prefl
  | mu f ih =>
    simp [←Formula.subst_comp, Subst.comp_def]; simp_vec
    prw [and_imp_iff]
    papply exists_elim'
    pintro; simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def]; simp [Term.shift_subst_lift, ←Term.shift_def]
    pintros 2
    prw [and_imp_iff]
    papply exists_elim'
    pintro; simp [Formula.shift, ←Formula.subst_comp, Subst.comp_def]; simp [Term.shift_subst_lift, ←Term.shift_def]
    pintros
    prw [←double_neg_iff, LO.ne_iff_lt_or_gt]
    papply or_elim'
    · pintro
      papply forall_elim ↑ₜ↑ₜt₁ at 1; simp [←Formula.subst_comp, Subst.comp_def, Term.shift_subst_single]
      papplya 1 at 0
      papply succ_ne_zero (t := #1)
      papply ih <;> passumption
    · pintro
      papply forall_elim ↑ₜ↑ₜt₂ at 3; simp [←Formula.subst_comp, Subst.comp_def, Term.shift_subst_single]
      papplya 3 at 0
      papply succ_ne_zero (t := #0)
      papply ih <;> passumption

set_option maxHeartbeats 300000

theorem repPrim_total {f : Primrec n} (σ) : ↑ᵀ^[k] PA ⊢ ∃' (repPrim f)[⇑ₛσ]ₚ := by
  induction f generalizing k with simp [repPrim, Partrec.ofPrim, rep]
  | const m => papply exists_intro m; simp; prefl
  | succ => papply exists_intro (S (σ 0)); simp [Term.shift_subst_single]; prefl
  | proj i => papply exists_intro (σ i); simp [Term.shift_subst_single]; prefl
  | comp f g ih₁ ih₂ =>
    simp [Formula.subst_exN, Formula.subst_andN, ←Formula.subst_comp, Subst.comp_def]
    papply existsN_elim
    · papply existsN_andN_of_andN_exists
      apply andN_intro
      intro i
      pexact ih₂ i σ
    apply forallN_intro
    pintro; simp
    papply exists_elim
    · pexact ih₁ (λ i => #(i.castAdd' k))
    pintros 2
    simp [Formula.shiftN_eq_subst]
    papply exists_intro #0
    simp [Formula.subst_exN]
    papply existsN_intro λ i => #(i.castAdd' k).succ
    simp [Term.shift, Formula.shift, Term.shiftN_eq_subst, Formula.subst_andN, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Vec.append_left]
    papply and_intro <;> passumption
  | prec f g ih₁ ih₂ =>
    simp [←Formula.subst_comp, Subst.comp_def]; simp [Subst.lift]
    psuffices ∀[≺ S (σ 0)] ∃' (
      ∃' ((rep (Partrec.ofPrim f))[#0 ∷ᵥ fun x => ↑ₜ↑ₜ↑ₜ(σ x.succ)]ₚ ⩑ beta (#0) (#1) 0)
      ⩑ ∀[≺ #1] ∃' ∃'
        ((rep (Partrec.ofPrim g))[#0 ∷ᵥ #2 ∷ᵥ #1 ∷ᵥ fun x => ↑ₜ↑ₜ↑ₜ↑ₜ↑ₜ(σ x.succ)]ₚ ⩑ beta #1 #3 #2 ⩑ beta (#0) (#3) (S #2)))
    · papply forall_elim (σ 0) at 0; simp [Term.shift_subst_single]
      phave σ 0 ≺ S (σ 0)
      · pexact lt_succ_self
      papplya 1 at 0; pclear 1
      papply exists_min at 0
      prevert
      papply exists_elim'
      pintro; prw [and_imp_iff, and_imp_iff]; pintros 3
      papply exists_elim
      · pexact beta_total #0 ↑ₜ(σ 0)
      pintros 2
      papply exists_intro #0
      papply exists_intro #1
      simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
      papply and_intro
      · passumption
      papply and_intro
      · passumption
      papply and_intro
      · passumption
      · pintros 2
        papply forall_elim #0 at 2
        simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
        papplya 2 at 0; pclear 2
        prw [neg_and_iff, neg_exists_iff, Order.neg_bdall_iff] at 0
        prevert
        papply or_elim'
        · pintro
          papply or_inl
          papply exists_elim
          · pexact ih₁ λ x => ↑ₜ↑ₜ↑ₜ(σ x.succ)
          pintros 2
          papply exists_intro #0
          simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
          papply and_intro
          · passumption 0
          · prw [nbeta_iff]
            pintro
            papply forall_elim #0 at 2
            simp [←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.single]
            prw [neg_and_iff, ←imp_iff] at 2
            papplya 2 <;> passumption
        · papply exists_elim'
          pintro; prw [and_imp_iff, neg_exists_iff]; pintros 2
          papply or_inr
          papply exists_intro #0
          simp [Term.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
          papply and_intro
          · passumption
          · papply exists_elim
            · pexact beta_total #1 #0
            pintros 2
            papply exists_elim
            · pexact ih₂ (#1 ∷ᵥ #0 ∷ᵥ fun x => ↑ₜ↑ₜ↑ₜ↑ₜ↑ₜ(σ x.succ))
            pintros 2
            papply exists_intro #1
            papply exists_intro #0
            simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
            simp_vec; simp [←Term.subst_comp, Subst.comp_def]
            papply and_intro
            · passumption
            papply and_intro
            · passumption
            · prw [nbeta_iff]
              pintro
              papply forall_elim #1 at 3; simp
              prw [neg_exists_iff] at 3
              papply forall_elim #0 at 3
              simp [←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
              prw [neg_and_iff, ←imp_iff, neg_and_iff, ←imp_iff] at 3
              papplya 3 <;> passumption
    · papply ind <;> simp [Term.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single, Subst.assign]
      · pintro; pclear 0
        papply exists_elim
        · pexact ih₁ λ x => (σ x.succ)
        pintros 2
        papply exists_elim
        · papply beta_comprehension' 1 (#0 ≐ #2)
          pintros 2
          papply exists_intro #1; simp [Subst.single]
          prefl
        pintros 2
        papply forall_elim 0 at 0; simp [Subst.lift]
        papply exists_elim
        · papplya 0; pexact zero_lt_succ
        pclear 0; pintro; prw [and_imp_iff]; pintros 2
        papply exists_intro #1
        papply and_intro
        · papply exists_intro #2
          simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.single]
          papply and_intro
          · passumption
          · prw [←1]; passumption
        · pintros 2; simp
          papply not_lt_zero at 0
          papply false_elim
          passumption
      · pintros 3
        prw [succ_lt_succ_iff] at 0
        papply lt_succ_of_lt at 0
        papplya 1 at 0; pclear 1
        prevert; papply exists_elim'
        pintro; prw [and_imp_iff]; pintros 2
        papply exists_elim
        · pexact beta_total #0 #1
        pintros 2
        papply exists_elim
        · pexact ih₂ (#2 ∷ᵥ #0 ∷ᵥ λ x => ↑ₜ↑ₜ↑ₜ(σ x.succ))
        pintros 2
        papply exists_elim
        · papply beta_comprehension' (S (S #3)) ((#1 ⪯ #5 ⇒ beta #0 #4 #1) ⩑ (#1 ≐ S #5 ⇒ #0 ≐ #2))
          pintro; simp
          prw [lt_succ_iff_le, PO.le_iff_lt_or_eq]
          papply or_elim'
          · pintro
            papply exists_elim
            · pexact beta_total #3 #0
            pintros 2
            papply exists_intro #0; simp [Subst.lift, Subst.single]
            papply and_intro
            · pintro; passumption
            · pintro; prw [0] at 2; papply PO.lt_irrefl at 2; papply false_elim; passumption
          · pintro
            papply exists_intro #1; simp [Subst.single]
            papply and_intro
            · pintro; prw [1, succ_le_iff_lt] at 0; papply PO.lt_irrefl at 0; papply false_elim; passumption
            · pintro; prefl
        pintros 2
        papply exists_intro #0
        simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
        papply and_intro
        · papply exists_elim
          · passumption 4
          pintro; prw [and_imp_iff]; pintros 2
          papply exists_intro #0
          simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
          papply and_intro
          · passumption
          · papply forall_elim 0 at 2
            papply exists_elim
            · papplya 2; simp [Subst.single]; pexact zero_lt_succ
            pintro; simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
            prw [and_imp_iff]; pintros 2
            papply and_left at 1
            psuffices #1 ≐ #0
            · prw [0]; passumption
            papply beta_unique
            · passumption 2
            · papplya 1; pexact zero_le
        · pintro; simp
          prw [lt_succ_iff_le, PO.le_iff_lt_or_eq]
          papply or_elim'
          · pintro; simp [Formula.shift]
            papply forall_elim #0 at 4; simp
            papply exists_elim
            · papplya 4; passumption 0
            pclear 4; pintro; papply exists_elim'
            pintro; prw [and_imp_iff, and_imp_iff]; pintros 3
            papply exists_intro #1
            papply exists_intro #0
            simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
            papply and_intro
            · passumption
            · papply and_intro
              · papply forall_elim #2 at 4; simp [Subst.single]
                papply exists_elim
                · papplya 4; papply lt_succ_of_lt; papply lt_succ_of_lt; passumption
                pclear 4; pintro; simp [Subst.lift]
                prw [and_imp_iff]; pintros 2
                papply and_left at 1
                psuffices #2 ≐ #0
                · prw [0]; passumption
                papply beta_unique
                · passumption 3
                · papplya 1; papply PO.le_of_lt; passumption
              · papply forall_elim (S #2) at 4; simp [Subst.single]
                papply exists_elim
                · papplya 4; prw [succ_lt_succ_iff]; papply lt_succ_of_lt; passumption
                pclear 4; pintro; simp [Subst.lift, Subst.single]
                prw [and_imp_iff]; pintros 2
                papply and_left at 1
                psuffices #1 ≐ #0
                · prw [0]; passumption
                papply beta_unique
                · passumption 2
                · papplya 1; prw [succ_le_iff_lt]; passumption
          · pintro
            papply exists_intro #3
            papply exists_intro #2
            simp_vec; simp [Term.shift, Formula.shift, ←Term.subst_comp, ←Formula.subst_comp, Subst.comp_def, Subst.lift, Subst.single]
            prw [0]; papply and_intro
            · passumption
            · papply and_intro
              · papply forall_elim #5 at 1; simp [Subst.single]
                papply exists_elim
                · papplya 1; papply lt_succ_of_lt; pexact lt_succ_self
                pclear 1; pintro; simp [Subst.lift]
                prw [and_imp_iff]; pintros 2
                papply and_left at 1
                psuffices #4 ≐ #0
                · prw [0]; passumption
                papply beta_unique
                · passumption 4
                · papplya 1; pexact PO.le_refl
              · papply forall_elim (S #5) at 1; simp [Subst.single]
                papply exists_elim
                · papplya 1; prw [succ_lt_succ_iff]; pexact lt_succ_self
                pclear 1; pintro; simp [Subst.lift]
                prw [and_imp_iff]; pintros 2
                papply and_right at 1
                phave S #6 ≐ S #6
                · prefl
                papplya 2 at 0
                prw [←0]
                passumption

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
  | zero => simp [prec_eval_zero, zeroPR_eval n]
  | succ m ih => simp [prec_eval_succ, ih, succPR_eval]

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
    simp [←Formula.subst_comp, Subst.lift, Vec.eq_one]
    intro x
    constructor
    · rw [Enumerable.mem_iff]; intro ⟨n, h₁⟩
      papply Proof.exists_intro n
      simp [←Formula.subst_comp]
      apply repRel_of_pos at h₁; simp_vec at h₁
      pexact h₁
    · intro h₁
      by_contra h₂; rw [Enumerable.not_mem_iff] at h₂
      refine h _ ⟨h₁, ?_⟩
      intro n; specialize h₂ n
      apply neg_repRel_of_zero at h₂; simp_vec at h₂
      simp [←Formula.subst_comp, Subst.cons_comp, Vec.eq_nil]
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
