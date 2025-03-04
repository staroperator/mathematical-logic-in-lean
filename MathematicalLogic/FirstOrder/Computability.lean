import MathematicalLogic.Computability.Partrec
import MathematicalLogic.FirstOrder.Encoding
import MathematicalLogic.FirstOrder.Proof

namespace FirstOrder.Language

open Primrec

section

variable {𝓛 : Language} [∀ n, Encodable (𝓛.Func n)]

def Term.funcPR : Primrec 3 :=
  succ.comp₁ (mul.comp₂ (const 2) (pair.comp₂ (proj 0) (pair.comp₂ (proj 1) (proj 2))))
@[simp] theorem Term.funcPR_eval {v : Vec (𝓛.Term n) m} :
  funcPR [m, Encodable.encode f, Encodable.encode v]ᵥ = Encodable.encode (f ⬝ᶠ v) := by
  simp [funcPR, Term.encode_func]

def Term.substPR : Primrec 2 :=
  (covrec (
    ite (odd.comp₁ (proj 0))
      (succ.comp₁ (mul.comp₂ (const 2)
        (pair.comp₂ (fst.comp₁ (div2.comp₁ (proj 0)))
          (pair.comp₂ (fst.comp₁ (snd.comp₁ (div2.comp₁ (proj 0))))
            (vmap'.comp₃ (fst.comp₁ (div2.comp₁ (proj 0)))
              (snd.comp₁ (snd.comp₁ (div2.comp₁ (proj 0))))
              (proj 1))))))
      (vget.comp₂ (proj 2) (div2.comp₁ (proj 0)))))
theorem Term.substPR_eval {t : 𝓛.Term n} {σ : 𝓛.Subst n m} :
  substPR [Encodable.encode t, Encodable.encode σ]ᵥ = Encodable.encode (t[σ]ₜ) := by
  induction t with
  | var x => rw [substPR, covrec_eval]; simp [Vec.encode_eq, Term.encode_var]; rw [vget_eval]
  | func f v ih =>
    rw [substPR, covrec_eval, ←substPR]; simp [Vec.encode_eq, Term.encode_func]; rw [vmap'_eval]
    · simp [←Vec.encode_eq, ih]
    · intro i; simp [Nat.lt_succ]
      apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
      apply (Nat.right_le_pair _ _).trans'
      apply (Nat.right_le_pair _ _).trans'
      apply Vec.le_paired (i := i)

def Subst.shiftPR : Primrec 1 :=
  vmk (mul.comp₂ (const 2) (succ.comp₁ (proj 0)))
theorem Subst.shiftPR_eval : shiftPR [n]ᵥ = Encodable.encode (shift : 𝓛.Subst n (n + 1)) := by
  simp [shiftPR, vmk_eval, Vec.encode_eq, Term.encode_var]

def Term.shiftPR : Primrec 2 :=
  substPR.comp₂ (proj 1) (Subst.shiftPR.comp₁ (proj 0))
theorem Term.shiftPR_eval {t : 𝓛.Term n} :
  shiftPR [n, Encodable.encode t]ᵥ = Encodable.encode (↑ₜt) := by
  simp [shiftPR, Subst.shiftPR_eval (𝓛 := 𝓛), Term.substPR_eval, Term.shift]

def Subst.liftPR : Primrec 3 :=
  pair.comp₂ zero ((vmap (Term.shiftPR.swap)).comp₃ (proj 0) (proj 2) (proj 1))
theorem Subst.liftPR_eval {σ : 𝓛.Subst n m} :
  liftPR [n, m, Encodable.encode σ]ᵥ = Encodable.encode (⇑ₛσ) := by
  simp [liftPR, lift]
  simp [Vec.encode_eq, vmap_eval, Term.shiftPR_eval, Term.encode_var]

def Subst.liftNPR : Primrec 4 :=
  (proj 2).prec (liftPR.comp₃ (add.comp₂ (proj 2) (proj 0)) (add.comp₂ (proj 3) (proj 0)) (proj 1))
theorem Subst.liftNPR_eval {σ : 𝓛.Subst n m} :
  liftNPR [k, n, m, Encodable.encode σ]ᵥ = Encodable.encode (⇑ₛ^[k] σ) := by
  simp [liftNPR]
  induction k generalizing n m σ with simp [liftN]
  | zero => simp [prec_eval_zero]
  | succ k ih => simp [prec_eval_succ, ih, liftPR_eval]

def Subst.singlePR : Primrec 2 :=
  pair.comp₂ (proj 1) ((vmk (mul.comp₂ (const 2) (proj 0))).comp₁ (proj 0))
theorem Subst.singlePR_eval {t : 𝓛.Term n} :
  singlePR [n, Encodable.encode t]ᵥ = Encodable.encode (↦ₛ t : 𝓛.Subst (n + 1) n) := by
  simp [singlePR, vmk_eval, Subst.single]
  simp [Vec.encode_eq, Term.encode_var]

def Subst.assignPR : Primrec 2 :=
  pair.comp₂ (proj 1) ((vmk (mul.comp₂ (const 2) (succ.comp₁ (proj 0)))).comp₁ (proj 0))
theorem Subst.assignPR_eval {t : 𝓛.Term (n + 1)} :
  assignPR [n, Encodable.encode t]ᵥ = Encodable.encode (≔ₛ t : 𝓛.Subst (n + 1) (n + 1)) := by
  simp [assignPR, vmk_eval, Subst.assign]
  simp [Vec.encode_eq, Term.encode_var]



variable [∀ n, Encodable (𝓛.Rel n)]

def Formula.relPR : Primrec 3 :=
  add.comp₂ (mul.comp₂ (const 4) (pair.comp₂ (proj 0) (pair.comp₂ (proj 1) (proj 2)))) (const 1)
@[simp] theorem Formula.relPR_eval {v : Vec (𝓛.Term n) m} :
  relPR [m, Encodable.encode r, Encodable.encode v]ᵥ = Encodable.encode (r ⬝ʳ v) := by
  simp [relPR, Formula.encode_rel]

def Formula.eqPR : Primrec 2 :=
  add.comp₂ (mul.comp₂ (const 4) (pair.comp₂ (proj 0) (proj 1))) (const 2)
@[simp] theorem Formula.eqPR_eval {t₁ t₂ : 𝓛.Term n} :
  eqPR [Encodable.encode t₁, Encodable.encode t₂]ᵥ = Encodable.encode (t₁ ≐ t₂) := by
  simp [eqPR, Formula.encode_eq]

def Formula.impPR : Primrec 2 :=
  add.comp₂ (mul.comp₂ (const 4) (pair.comp₂ (proj 0) (proj 1))) (const 3)
@[simp] theorem Formula.impPR_eval {p q : 𝓛.Formula n} :
  impPR [Encodable.encode p, Encodable.encode q]ᵥ = Encodable.encode (p ⇒ q) := by
  simp [impPR, Formula.encode_imp]

def Formula.negPR : Primrec 1 :=
  impPR.comp₂ (proj 0) zero
@[simp] theorem Formula.negPR_eval {p : 𝓛.Formula n} :
  negPR [Encodable.encode p]ᵥ = Encodable.encode (~ p) := by
  simp [negPR]
  nth_rw 2 [←Formula.encode_false (𝓛 := 𝓛)]
  rw [impPR_eval]; rfl

def Formula.allPR : Primrec 1 :=
  add.comp₂ (mul.comp₂ (const 4) (proj 0)) (const 4)
@[simp] theorem Formula.allPR_eval {p : 𝓛.Formula (n + 1)} :
  allPR [Encodable.encode p]ᵥ = Encodable.encode (∀' p) := by
  simp [allPR, Formula.encode_all]

def Formula.andPR : Primrec 2 :=
  negPR.comp₁ (impPR.comp₂ (proj 0) (negPR.comp₁ (proj 1)))
@[simp] theorem Formula.andPR_eval {p q : 𝓛.Formula n} :
  andPR [Encodable.encode p, Encodable.encode q]ᵥ = Encodable.encode (p ⩑ q) := by
  simp [andPR, PropNotation.and]

def Formula.andNPR : Primrec 2 :=
  ((Formula.negPR.comp₁ zero).prec (Formula.andPR.comp₂
    (vget.comp₂ (proj 3) (sub.comp₂ (proj 2) (succ.comp₁ (proj 0))))
    (proj 1))).comp₃ (proj 0) (proj 0) (proj 1)
@[simp] theorem Formula.andNPR_eval {v : Vec (𝓛.Formula n) m} :
  andNPR [m, Encodable.encode v]ᵥ = Encodable.encode (⋀ i, v i) := by
  simp [andNPR]
  generalize h : prec _ _ = f
  suffices ∀ k (h₁ : k ≤ m), f [k, m, Encodable.encode v]ᵥ = Encodable.encode (⋀ (j : Fin k), v ⟨m - k + j, Nat.add_lt_of_lt_sub (Nat.sub_lt_sub_left ((Fin.is_lt _).trans_le h₁) (Fin.is_lt _))⟩) by
    specialize this m (by rfl)
    simp at this
    exact this
  intro k h₁
  induction k with
  | zero => rw [←h, prec_eval_zero]; simp [Formula.andN]; rfl
  | succ k ih =>
    rw [←h, prec_eval_succ, h]
    simp; rw [ih (Nat.le_of_succ_le h₁), Vec.encode_eq, vget_eval' (by simp; exact Nat.zero_lt_of_lt h₁), andPR_eval]
    congr
    ext i
    simp [Vec.tail, Function.comp_def]
    congr 2
    rw [←Nat.sub_sub, ←Nat.add_assoc,
      ←Nat.sub_add_comm (n := m - k) (Nat.le_sub_of_add_le (by simp [Nat.add_comm, h₁])),
      Nat.sub_add_cancel (Nat.le_add_right_of_le (Nat.le_sub_of_add_le (by simp [Nat.add_comm, h₁])))]

def Formula.depth : 𝓛.Formula n → ℕ
| p ⇒ q => max p.depth q.depth
| ∀' p => p.depth + 1
| _ => 0

def Formula.depthPR : Primrec 1 :=
  covrec (ite (not (proj 0)) zero
    (ite (Primrec.eq (mod.comp₂ (proj 0) (const 4)) (const 3))
      (max.comp₂
        (vget.comp₂ (proj 1) (fst.comp₁ (div.comp₂ (proj 0) (const 4))))
        (vget.comp₂ (proj 1) (snd.comp₁ (div.comp₂ (proj 0) (const 4)))))
      (ite (Primrec.eq (mod.comp₂ (proj 0) (const 4)) (const 0))
        (succ.comp₁ (vget.comp₂ (proj 1) (pred.comp₁ (div.comp₂ (proj 0) (const 4)))))
        zero)))
theorem Formula.depthPR_eval {p : 𝓛.Formula n} :
  depthPR [Encodable.encode p]ᵥ = p.depth := by
  induction p with simp [depth]
  | imp p q ih₁ ih₂ =>
    simp [Formula.encode_imp]
    rw [depthPR, covrec_eval, ←depthPR]
    simp [Nat.mul_add_mod, Vec.eq_two]
    simp [Nat.mul_add_div]
    rw [vget_eval', vget_eval']; simp [ih₁, ih₂]
    all_goals
      apply Nat.succ_le_succ
      apply (Nat.le_add_right _ _).trans'
      apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
      first | apply Nat.left_le_pair | apply Nat.right_le_pair
  | all p ih =>
    simp [Formula.encode_all]
    rw [depthPR, covrec_eval, ←depthPR]
    simp [Nat.mul_add_mod, Vec.eq_two, Vec.head]
    simp [Nat.mul_add_div]
    rw [vget_eval']; simp [ih]
    apply Nat.succ_le_succ
    apply (Nat.le_add_right _ _).trans'
    apply Nat.le_mul_of_pos_left
    simp
  | _ => rw [depthPR, covrec_eval]; simp [Nat.mul_add_mod, Formula.encode_rel, Formula.encode_eq, Formula.encode_false]

def Formula.substPR : Primrec 4 :=
  (paired (covrec (unpaired
    (ite (not (proj 0)) zero
      (ite (Primrec.eq (mod.comp₂ (proj 0) (const 4)) (const 1))
        (add.comp₂ (mul.comp₂ (const 4)
          (pair.comp₂ (fst.comp₁ (div.comp₂ (proj 0) (const 4)))
            (pair.comp₂ (fst.comp₁ (snd.comp₁ (div.comp₂ (proj 0) (const 4))))
              ((vmap (Term.substPR.comp₂ (proj 0) (proj 1))).comp₃
                (fst.comp₁ (div.comp₂ (proj 0) (const 4)))
                (snd.comp₁ (snd.comp₁ (div.comp₂ (proj 0) (const 4))))
                (Subst.liftNPR.comp₄
                  (sub.comp₂ (proj 3) (proj 1)) (proj 4) (proj 5) (proj 6)))))) (const 1))
        (ite (Primrec.eq (mod.comp₂ (proj 0) (const 4)) (const 2))
          (add.comp₂ (mul.comp₂ (const 4)
            (pair.comp₂
              (Term.substPR.comp₂
                (fst.comp₁ (div.comp₂ (proj 0) (const 4)))
                (Subst.liftNPR.comp₄
                  (sub.comp₂ (proj 3) (proj 1)) (proj 4) (proj 5) (proj 6)))
              (Term.substPR.comp₂
                (snd.comp₁ (div.comp₂ (proj 0) (const 4)))
                (Subst.liftNPR.comp₄
                  (sub.comp₂ (proj 3) (proj 1)) (proj 4) (proj 5) (proj 6))))) (const 2))
          (ite (Primrec.eq (mod.comp₂ (proj 0) (const 4)) (const 3))
            (add.comp₂ (mul.comp₂ (const 4)
              (pair.comp₂
                (vget.comp₂ (proj 2)
                  (pair.comp₂
                    (fst.comp₁ (div.comp₂ (proj 0) (const 4)))
                    (proj 1)))
                (vget.comp₂ (proj 2)
                  (pair.comp₂
                    (snd.comp₁ (div.comp₂ (proj 0) (const 4)))
                    (proj 1))))) (const 3))
            (add.comp₂ (mul.comp₂ (const 4)
              (vget.comp₂ (proj 2)
                (pair.comp₂
                  (pred.comp₁ (div.comp₂ (proj 0) (const 4)))
                  (pred.comp₁ (proj 1))))) (const 4))))))
  ))).comp₆ (proj 2) (depthPR.comp₁ (proj 2)) (depthPR.comp₁ (proj 2)) (proj 0) (proj 1) (proj 3)
theorem Formula.substPR_eval {p : 𝓛.Formula n} {σ : 𝓛.Subst n m} :
  substPR [n, m, Encodable.encode p, Encodable.encode σ]ᵥ = Encodable.encode (p[σ]ₚ) := by
  simp [substPR, Vec.eq_four]; simp
  generalize h : covrec _ = f
  suffices ∀ d k l (p : 𝓛.Formula l) (h₁ : l = n + k), d ≥ p.depth →
    f [(Encodable.encode p).pair d, d + k, n, m, Encodable.encode σ]ᵥ = Encodable.encode ((h₁ ▸ p)[⇑ₛ^[k] σ]ₚ) by
    simp [depthPR_eval]
    specialize this p.depth 0 n p rfl (by rfl)
    simp at this
    exact this
  intro d k l p h₁ h₂
  induction p generalizing d k with simp [depth] at h₂
  | rel r v =>
    subst h₁; rw [←h, covrec_eval, h]; simp [Formula.encode_rel, Nat.mul_add_mod, Nat.mul_add_div]
    simp [Vec.encode_eq, vmap_eval]
    congr with i
    simp [Vec.eq_four]; simp [←Vec.encode_eq, Subst.liftNPR_eval, Term.substPR_eval]
  | eq t₁ t₂ =>
    subst h₁; rw [←h, covrec_eval, h]; simp [Formula.encode_eq, Nat.mul_add_mod, Nat.mul_add_div]
    constructor <;> simp [Vec.eq_four] <;> simp [←Vec.encode_eq, Subst.liftNPR_eval, Term.substPR_eval]
  | false => subst h₁; rw [←h, covrec_eval]; simp [Formula.encode_false]
  | imp p q ih₁ ih₂ =>
    subst h₁; rw [←h, covrec_eval, h]; simp [Formula.encode_imp, Nat.mul_add_mod, Nat.mul_add_div]
    constructor
    · rw [vget_eval']
      · rw [ih₁ d k rfl h₂.left]
      · apply Nat.pair_lt_pair_left
        simp [Nat.lt_succ]
        apply (Nat.le_add_right _ _).trans'
        apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
        apply Nat.left_le_pair
    · rw [vget_eval']
      · rw [ih₂ d k rfl h₂.right]
      · apply Nat.pair_lt_pair_left
        simp [Nat.lt_succ]
        apply (Nat.le_add_right _ _).trans'
        apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
        apply Nat.right_le_pair
  | all p ih =>
    cases' d with d <;> simp at h₂
    subst h₁; rw [←h, covrec_eval, h]; simp [Formula.encode_all, Nat.mul_add_mod, Nat.mul_add_div]
    rw [vget_eval']
    · rw [Nat.add_right_comm d 1 k, Nat.add_assoc d k 1, ih d (k + 1) rfl h₂, Subst.liftN]
    · apply Nat.pair_lt_pair_left'
      · simp [Nat.lt_succ]
        apply (Nat.le_add_right _ _).trans'
        exact Nat.le_mul_of_pos_left _ (by simp)
      · simp

def Formula.shiftPR : Primrec 2 :=
  substPR.comp₄ (proj 0) (succ.comp₁ (proj 0)) (proj 1) (Subst.shiftPR.comp₁ (proj 0))
theorem Formula.shiftPR_eval {p : 𝓛.Formula n} :
  shiftPR [n, Encodable.encode p]ᵥ = Encodable.encode (↑ₚp) := by
  simp [shiftPR, Subst.shiftPR_eval (𝓛 := 𝓛), substPR_eval, Formula.shift]

def Formula.substSinglePR : Primrec 3 :=
  substPR.comp₄ (succ.comp₁ (proj 0)) (proj 0) (proj 1) (Subst.singlePR.comp₂ (proj 0) (proj 2))
theorem Formula.substSinglePR_eval {p : 𝓛.Formula (n + 1)} {t : 𝓛.Term n} :
  substSinglePR [n, Encodable.encode p, Encodable.encode t]ᵥ = Encodable.encode (p[↦ₛ t]ₚ) := by
  simp [substSinglePR, Subst.singlePR_eval, substPR_eval]

def Formula.substAssignPR : Primrec 3 :=
  substPR.comp₄ (succ.comp₁ (proj 0)) (succ.comp₁ (proj 0)) (proj 1) (Subst.assignPR.comp₂ (proj 0) (proj 2))
theorem Formula.substAssignPR_eval {p : 𝓛.Formula (n + 1)} {t : 𝓛.Term (n + 1)} :
  substAssignPR [n, Encodable.encode p, Encodable.encode t]ᵥ = Encodable.encode (p[≔ₛ t]ₚ) := by
  simp [substAssignPR, Subst.assignPR_eval, substPR_eval]

end



section

variable (𝓛 : Language) [∀ n, Encodable (𝓛.Func n)] [∀ n, Encodable (𝓛.Rel n)]

-- should be replaced with `FinEncodable (𝓛.Func n)` and `FinEncodable (𝓛.Rel n)` in the future
class PrimCodable where
  isFuncPR : Primrec 2
  isFuncPR_eval_pos_iff : ∀ {n m}, 0 < isFuncPR [n, m]ᵥ ↔ ∃ (f : 𝓛.Func n), m = Encodable.encode f
  isRelPR : Primrec 2
  isRelPR_eval_pos_iff : ∀ {n m}, 0 < isRelPR [n, m]ᵥ ↔ ∃ (r : 𝓛.Rel n), m = Encodable.encode r

open PrimCodable

variable [𝓛.PrimCodable]

def isTermPR : Primrec 2 :=
  (covrec (
    ite (odd.comp₁ (proj 0))
      (andv [
        (isFuncPR 𝓛).comp₂ (fst.comp₁ (div2.comp₁ (proj 0))) (fst.comp₁ (snd.comp₁ (div2.comp₁ (proj 0)))),
        isvec.comp₂ (fst.comp₁ (div2.comp₁ (proj 0))) (snd.comp₁ (snd.comp₁ (div2.comp₁ (proj 0)))),
        vand.comp₂ (fst.comp₁ (div2.comp₁ (proj 0)))
          (vmap'.comp₃ (fst.comp₁ (div2.comp₁ (proj 0))) (snd.comp₁ (snd.comp₁ (div2.comp₁ (proj 0)))) (proj 1))
      ]ᵥ)
      (lt (div2.comp₁ (proj 0)) (proj 2)))).swap
theorem isTermPR_eval_pos_iff : 0 < 𝓛.isTermPR [n, m]ᵥ ↔ ∃ (t : 𝓛.Term n), m = Encodable.encode t := by
  constructor
  · intro h; simp [isTermPR] at h
    induction' m using Nat.strong_induction_on with m ih
    rw [covrec_eval] at h; simp at h; split at h
    next h' =>
      simp at h; rcases h with ⟨h₁, h₂, h₃⟩
      simp [PrimCodable.isFuncPR_eval_pos_iff] at h₁; rcases h₁ with ⟨f, h₁⟩
      simp [isvec_eval_pos_iff] at h₂; rcases h₂ with ⟨v, h₂⟩
      have h'' : ∀ i, v i < m := by
        intro i
        apply lt_of_le_of_lt (Vec.le_paired (i := i))
        rw [←h₂]
        apply lt_of_le_of_lt (Nat.unpair_right_le _)
        apply lt_of_le_of_lt (Nat.unpair_right_le _)
        conv => rhs; rw [←m.bodd_add_div2]
        simp [h', Nat.one_add, Nat.lt_succ_iff]
        apply Nat.le_mul_of_pos_left
        simp
      rw [h₂, vmap'_eval h''] at h₃
      simp [vand_eval_pos_iff] at h₃
      replace h₃ := λ i => ih _ (h'' i) (h₃ i)
      choose v h₃ using h₃
      exists f ⬝ᶠ v
      simp [Term.encode_func, Vec.encode_eq, ←h₁, ←h₃, ←h₂]
      nth_rw 1 [←m.bodd_add_div2]
      simp [h', Nat.one_add]
    next h' =>
      simp at h
      exists #⟨m.div2, h⟩
      simp [Term.encode_var, Nat.div2_val]; rw [←m.bodd_add_div2]; simp [h']
  · rintro ⟨t, rfl⟩; simp [isTermPR]
    induction t with
    | var x => rw [covrec_eval]; simp [Term.encode_var, Nat.div2_val]
    | func f v ih =>
      rw [covrec_eval]
      simp [Vec.eq_two, Vec.eq_three]
      simp [Term.encode_func, Nat.div2_val, PrimCodable.isFuncPR_eval_pos_iff, isvec_eval_pos_iff, Vec.encode_eq]
      rw [vmap'_eval]
      · simp [vand_eval_pos_iff]; exact ih
      · intro i
        apply Nat.succ_le_succ
        apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
        apply (Nat.right_le_pair _ _).trans'
        apply (Nat.right_le_pair _ _).trans'
        apply Vec.le_paired (i := i)

def isFormulaPR : Primrec 2 :=
  (paired (covrec (unpaired (
    ite (not (proj 0))
      (const 1)
      (ite (eq (mod.comp₂ (proj 0) (const 4)) (const 1))
        (andv [
          (isRelPR 𝓛).comp₂ (fst.comp₁ (div.comp₂ (proj 0) (const 4))) (fst.comp₁ (snd.comp₁ (div.comp₂ (proj 0) (const 4)))),
          isvec.comp₂ (fst.comp₁ (div.comp₂ (proj 0) (const 4))) (snd.comp₁ (snd.comp₁ (div.comp₂ (proj 0) (const 4)))),
          vand.comp₂ (fst.comp₁ (div.comp₂ (proj 0) (const 4)))
              ((vmap 𝓛.isTermPR.swap).comp₃
                (fst.comp₁ (div.comp₂ (proj 0) (const 4)))
                (snd.comp₁ (snd.comp₁ (div.comp₂ (proj 0) (const 4))))
                (add.comp₂ (proj 4) (sub.comp₂ (proj 3) (proj 1)))
                )
        ]ᵥ)
        (ite (eq (mod.comp₂ (proj 0) (const 4)) (const 2))
          (and
            (𝓛.isTermPR.comp₂
              (add.comp₂ (proj 4) (sub.comp₂ (proj 3) (proj 1)))
              (fst.comp₁ (div.comp₂ (proj 0) (const 4))))
            (𝓛.isTermPR.comp₂
              (add.comp₂ (proj 4) (sub.comp₂ (proj 3) (proj 1)))
              (snd.comp₁ (div.comp₂ (proj 0) (const 4)))))
          (ite (eq (mod.comp₂ (proj 0) (const 4)) (const 3))
            (and
              (vget.comp₂ (proj 2) (pair.comp₂ (fst.comp₁ (div.comp₂ (proj 0) (const 4))) (proj 1)))
              (vget.comp₂ (proj 2) (pair.comp₂ (snd.comp₁ (div.comp₂ (proj 0) (const 4))) (proj 1))))
            (and
              (sign.comp₁ (proj 1))
              (vget.comp₂ (proj 2) (pair.comp₂ (pred.comp₁ (div.comp₂ (proj 0) (const 4))) (pred.comp₁ (proj 1))))))))
    )))).comp₄ (proj 1) (Formula.depthPR.comp₁ (proj 1)) (Formula.depthPR.comp₁ (proj 1)) (proj 0)
theorem isFormulaPR_eval_pos_iff : 0 < 𝓛.isFormulaPR [n, m]ᵥ ↔ ∃ (p : 𝓛.Formula n), m = Encodable.encode p := by
  simp [isFormulaPR, Vec.tail, Function.comp_def]
  rw [Vec.eq_two λ _ => _]; simp
  generalize h : covrec _ = f
  suffices ∀ d k l (h₁ : l = n + k),
    f [m.pair d, d + k, n]ᵥ > 0 ↔ ∃ (p : 𝓛.Formula l), m = Encodable.encode p ∧ d ≥ p.depth by
    specialize this (Formula.depthPR.eval [m]ᵥ) 0
    simp at this; rw [this]
    constructor
    · intro ⟨p, h, _⟩; exists p
    · intro ⟨p, h⟩; exists p, h; rw [h, Formula.depthPR_eval]
  intros d k l h₁
  constructor
  · subst h₁
    intro h₁
    induction' m using Nat.strong_induction_on with m ih generalizing d k
    rw [←h, covrec_eval, h] at h₁; simp at h₁; split at h₁
    next h₂ => exists ⊥; simp [Formula.encode_false, h₂, Formula.depth]
    next h₂ =>
      simp [Nat.ne_zero_iff_zero_lt] at h₂; split at h₁
      next h₃ =>
        simp at h₁; rcases h₁ with ⟨h₁, h₁', h₁''⟩
        simp [PrimCodable.isRelPR_eval_pos_iff] at h₁; rcases h₁ with ⟨r, h₁⟩
        simp [isvec_eval_pos_iff] at h₁'; rcases h₁' with ⟨v, h₁'⟩
        simp [h₁', vmap_eval, vand_eval_pos_iff, isTermPR_eval_pos_iff] at h₁''
        choose v h₁'' using h₁''
        exists r ⬝ʳ v
        simp [Formula.encode_rel, ←h₁, ←h₁', ←h₁'', Vec.encode_eq, Formula.depth]
        rw [←h₃, Nat.div_add_mod]
      next _ =>
        split at h₁
        next h₃ =>
          simp [isTermPR_eval_pos_iff] at h₁; rcases h₁ with ⟨⟨t₁, h₁⟩, t₂, h₁'⟩
          exists t₁ ≐ t₂
          simp [Formula.encode_eq, ←h₁, ←h₁', Formula.depth]
          rw [←h₃, Nat.div_add_mod]
        next _ =>
          split at h₁
          next h₃ =>
            simp [Vec.eq_two] at h₁; simp at h₁; rcases h₁ with ⟨h₁, h₁'⟩
            have : (Nat.unpair (m / 4)).1 < m :=
              (Nat.unpair_left_le _).trans_lt (Nat.div_lt_self h₂ (by simp))
            rw [vget_eval' (Nat.pair_lt_pair_left _ this)] at h₁
            apply ih _ this at h₁; rcases h₁ with ⟨p, h₁, h₁''⟩
            have : (Nat.unpair (m / 4)).2 < m := 
              (Nat.unpair_right_le _).trans_lt (Nat.div_lt_self h₂ (by simp))
            rw [vget_eval' (Nat.pair_lt_pair_left _ this)] at h₁'
            apply ih _ this at h₁'; rcases h₁' with ⟨q, h₁', h₁'''⟩
            exists p ⇒ q
            simp [Formula.encode_imp, ←h₁, ←h₁', Formula.depth, h₁'', h₁''']
            rw [←h₃, Nat.div_add_mod]
          next _ =>
            simp [Vec.eq_two] at h₁; simp at h₁
            cases' d with d <;> simp at h₁
            have : m / 4 - 1 < m := by
              apply lt_of_le_of_lt (Nat.pred_le _)
              apply Nat.div_lt_self _ (by simp)
              exact h₂
            rw [vget_eval' (Nat.pair_lt_pair_left' this (by simp)), Nat.add_right_comm] at h₁
            apply ih _ this d (k + 1) at h₁
            simp at h₁
            rcases h₁ with ⟨p, h₁, h₁'⟩
            exists ∀' p
            simp [Formula.encode_all, Formula.depth, h₁', ←h₁]
            rw [Nat.mul_sub_left_distrib, Nat.sub_add_cancel, Nat.mul_div_cancel']
            · match h₃ : m % 4 with
              | 0 => exact Nat.dvd_of_mod_eq_zero h₃
              | 1 | 2 | 3 => contradiction
              | _ + 4 =>
                have : m % 4 < 4 := Nat.mod_lt _ (by simp)
                rw [h₃] at this; contradiction
            · apply Nat.mul_le_mul_left
              rw [Nat.one_le_div_iff (by simp)]
              by_contra h
              match m with
              | 0 | 1 | 2 | 3 => contradiction
              | _ + 4 => simp at h
  · rintro ⟨p, rfl, h₂⟩
    induction p generalizing d k with subst h₁
    | rel r v =>
      rw [←h, covrec_eval, h]; simp [Formula.encode_rel, Nat.mul_add_mod, Nat.mul_add_div, Vec.eq_two]
      simp [PrimCodable.isRelPR_eval_pos_iff, isvec_eval_pos_iff, Vec.encode_eq, vmap_eval, vand_eval_pos_iff, isTermPR_eval_pos_iff]
    | eq t₁ t₂ =>
      rw [←h, covrec_eval, h]; simp [Formula.encode_eq, Nat.mul_add_mod, Nat.mul_add_div, Vec.eq_two]
      simp [isTermPR_eval_pos_iff]
    | false =>
      rw [←h, covrec_eval, h]; simp [Formula.encode_false]
    | imp p q ih₁ ih₂ =>
      simp [Formula.depth] at h₂
      rw [←h, covrec_eval, h]; simp [Formula.encode_imp, Nat.mul_add_mod, Nat.mul_add_div, Vec.eq_two]; simp
      constructor
      · rw [vget_eval']
        · exact ih₁ _ _ rfl h₂.left
        · apply Nat.pair_lt_pair_left
          apply Nat.succ_le_succ
          apply (Nat.le_add_right _ _).trans'
          apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
          apply Nat.left_le_pair
      · rw [vget_eval']
        · exact ih₂ _ _ rfl h₂.right
        · apply Nat.pair_lt_pair_left
          apply Nat.succ_le_succ
          apply (Nat.le_add_right _ _).trans'
          apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
          apply Nat.right_le_pair
    | all p ih =>
      simp [Formula.depth] at h₂
      cases' d with d <;> simp at h₂
      rw [←h, covrec_eval, h]; simp [Formula.encode_all, Nat.mul_add_mod, Nat.mul_add_div, Vec.eq_two]; simp [Nat.add_right_comm]
      rw [vget_eval']
      · exact ih d (k + 1) rfl h₂
      · apply Nat.pair_lt_pair_left'
        · apply Nat.succ_le_succ
          apply (Nat.le_add_right _ _).trans'
          apply Nat.le_mul_of_pos_left
          simp
        · simp

def isSentencePR : Primrec 1 := 𝓛.isFormulaPR.comp₂ (const 0) (proj 0)
theorem isSentencePR_eval_pos_iff : 0 < 𝓛.isSentencePR [k]ᵥ ↔ ∃ (p : 𝓛.Sentence), k = Encodable.encode p := by
  simp [isSentencePR, isFormulaPR_eval_pos_iff]

def isAxiomPR : Primrec 2 :=
  (paired (covrec (unpaired
    (orv [
      bdExists (proj 0) (bdExists (proj 1) (andv [
        𝓛.isFormulaPR.comp₂ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3))) (proj 1),
        𝓛.isFormulaPR.comp₂ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3))) (proj 0),
        eq (proj 2) (Formula.impPR.comp₂ (proj 1) (Formula.impPR.comp₂ (proj 0) (proj 1)))
      ]ᵥ)),
      bdExists (proj 0) (bdExists (proj 1) (bdExists (proj 2) (andv [
        𝓛.isFormulaPR.comp₂ (add.comp₂ (proj 7) (sub.comp₂ (proj 6) (proj 4))) (proj 2),
        𝓛.isFormulaPR.comp₂ (add.comp₂ (proj 7) (sub.comp₂ (proj 6) (proj 4))) (proj 1),
        𝓛.isFormulaPR.comp₂ (add.comp₂ (proj 7) (sub.comp₂ (proj 6) (proj 4))) (proj 0),
        eq (proj 3) (Formula.impPR.comp₂
          (Formula.impPR.comp₂ (proj 2) (Formula.impPR.comp₂ (proj 1) (proj 0)))
          (Formula.impPR.comp₂
            (Formula.impPR.comp₂ (proj 2) (proj 1))
            (Formula.impPR.comp₂ (proj 2) (proj 0))))
      ]ᵥ))),
      bdExists (proj 0) (bdExists (proj 1) (andv [
        𝓛.isFormulaPR.comp₂ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3))) (proj 1),
        𝓛.isFormulaPR.comp₂ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3))) (proj 0),
        eq (proj 2) (Formula.impPR.comp₂
          (Formula.impPR.comp₂ (Formula.negPR.comp₁ (proj 1)) (Formula.negPR.comp₁ (proj 0)))
          (Formula.impPR.comp₂ (proj 0) (proj 1)))
      ]ᵥ)),
      bdExists (proj 0) (bdExists (succ.comp₁ (proj 1)) (andv [
        𝓛.isFormulaPR.comp₂ (succ.comp₁ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3)))) (proj 1),
        𝓛.isTermPR.comp₂ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3))) (proj 0),
        eq (proj 2) (Formula.impPR.comp₂
          (Formula.allPR.comp₁ (proj 1))
          (Formula.substSinglePR.comp₃ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3))) (proj 1) (proj 0)))
      ]ᵥ)),
      bdExists (proj 0) (andv [
        𝓛.isFormulaPR.comp₂ (add.comp₂ (proj 5) (sub.comp₂ (proj 4) (proj 2))) (proj 0),
        eq (proj 1) (Formula.impPR.comp₂ (proj 0) (Formula.allPR.comp₁ (Formula.shiftPR.comp₂ (add.comp₂ (proj 5) (sub.comp₂ (proj 4) (proj 2))) (proj 0))))
      ]ᵥ),
      bdExists (proj 0) (bdExists (proj 1) (andv [
        𝓛.isFormulaPR.comp₂ (succ.comp₁ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3)))) (proj 1),
        𝓛.isFormulaPR.comp₂ (succ.comp₁ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3)))) (proj 0),
        eq (proj 2) (Formula.impPR.comp₂
          (Formula.allPR.comp₁ (Formula.impPR.comp₂ (proj 1) (proj 0)))
          (Formula.impPR.comp₂ (Formula.allPR.comp₁ (proj 1)) (Formula.allPR.comp₁ (proj 0))))
      ]ᵥ)),
      bdExists (proj 0) (andv [
        𝓛.isTermPR.comp₂ (add.comp₂ (proj 5) (sub.comp₂ (proj 4) (proj 2))) (proj 0),
        eq (proj 1) (Formula.eqPR.comp₂ (proj 0) (proj 0))
      ]ᵥ),
      bdExists (proj 0) (bdExists (proj 1) (andv [
        𝓛.isTermPR.comp₂ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3))) (proj 1),
        𝓛.isTermPR.comp₂ (add.comp₂ (proj 6) (sub.comp₂ (proj 5) (proj 3))) (proj 0),
        eq (proj 2) (Formula.impPR.comp₂
          (Formula.eqPR.comp₂ (proj 1) (proj 0))
          (Formula.eqPR.comp₂ (proj 0) (proj 1)))
      ]ᵥ)),
      bdExists (proj 0) (bdExists (proj 1) (bdExists (proj 2) (andv [
        𝓛.isTermPR.comp₂ (add.comp₂ (proj 7) (sub.comp₂ (proj 6) (proj 4))) (proj 2),
        𝓛.isTermPR.comp₂ (add.comp₂ (proj 7) (sub.comp₂ (proj 6) (proj 4))) (proj 1),
        𝓛.isTermPR.comp₂ (add.comp₂ (proj 7) (sub.comp₂ (proj 6) (proj 4))) (proj 0),
        eq (proj 3) (Formula.impPR.comp₂
          (Formula.eqPR.comp₂ (proj 2) (proj 1))
          (Formula.impPR.comp₂
            (Formula.eqPR.comp₂ (proj 1) (proj 0))
            (Formula.eqPR.comp₂ (proj 2) (proj 0))))
      ]ᵥ))),
      bdExists (proj 0) (bdExists (proj 1) (bdExists (proj 2) (bdExists (proj 3) (andv [
        (isFuncPR 𝓛).comp₂ (proj 3) (proj 2),
        isvec.comp₂ (proj 3) (proj 1),
        vand.comp₂ (proj 3) ((vmap 𝓛.isTermPR.swap).comp₃ (proj 3) (proj 1) (add.comp₂ (proj 8) (sub.comp₂ (proj 7) (proj 5)))),
        isvec.comp₂ (proj 3) (proj 0),
        vand.comp₂ (proj 3) ((vmap 𝓛.isTermPR.swap).comp₃ (proj 3) (proj 0) (add.comp₂ (proj 8) (sub.comp₂ (proj 7) (proj 5)))),
        eq (proj 4) (Formula.impPR.comp₂
          (Formula.andNPR.comp₂ (proj 3)
            ((vmk (Formula.eqPR.comp₂
              (vget.comp₂ (proj 1) (proj 0))
              (vget.comp₂ (proj 2) (proj 0)))).comp₃ (proj 3) (proj 1) (proj 0)))
          (Formula.eqPR.comp₂
            (Term.funcPR.comp₃ (proj 3) (proj 2) (proj 1))
            (Term.funcPR.comp₃ (proj 3) (proj 2) (proj 0))))
      ]ᵥ)))),
      bdExists (proj 0) (bdExists (proj 1) (bdExists (proj 2) (bdExists (proj 3) (andv [
        (isRelPR 𝓛).comp₂ (proj 3) (proj 2),
        isvec.comp₂ (proj 3) (proj 1),
        vand.comp₂ (proj 3) ((vmap 𝓛.isTermPR.swap).comp₃ (proj 3) (proj 1) (add.comp₂ (proj 8) (sub.comp₂ (proj 7) (proj 5)))),
        isvec.comp₂ (proj 3) (proj 0),
        vand.comp₂ (proj 3) ((vmap 𝓛.isTermPR.swap).comp₃ (proj 3) (proj 0) (add.comp₂ (proj 8) (sub.comp₂ (proj 7) (proj 5)))),
        eq (proj 4) (Formula.impPR.comp₂
          (Formula.andNPR.comp₂ (proj 3)
            ((vmk (Formula.eqPR.comp₂
              (vget.comp₂ (proj 1) (proj 0))
              (vget.comp₂ (proj 2) (proj 0)))).comp₃ (proj 3) (proj 1) (proj 0)))
          (Formula.impPR.comp₂
            (Formula.relPR.comp₃ (proj 3) (proj 2) (proj 1))
            (Formula.relPR.comp₃ (proj 3) (proj 2) (proj 0))))
      ]ᵥ)))),
      bdExists (proj 0) (andv [
        𝓛.isFormulaPR.comp₂ (succ.comp₁ (add.comp₂ (proj 5) (sub.comp₂ (proj 4) (proj 2)))) (proj 0),
        vget.comp₂ (proj 3) (pair.comp₂ (proj 0) (pred.comp₁ (proj 2))),
        eq (proj 1) (Formula.allPR.comp₁ (proj 0))
      ]ᵥ)
    ]ᵥ)))).comp₄ (proj 1) (Formula.depthPR.comp₁ (proj 1)) (Formula.depthPR.comp₁ (proj 1)) (proj 0)

set_option maxHeartbeats 1300000

theorem isAxiomPR_eval_pos_iff [HasConstEncodeZero 𝓛] {p : 𝓛.Formula n} :
  0 < 𝓛.isAxiomPR [n, Encodable.encode p]ᵥ ↔ p ∈ 𝓛.Axiom := by
  simp [isAxiomPR, Vec.tail, Function.comp_def]
  rw [Vec.eq_two λ _ => _]; simp
  generalize h : covrec _ = f
  suffices ∀ d k l (p : 𝓛.Formula l) (h₁ : l = n + k), d ≥ p.depth →
      (0 < f [(Encodable.encode p).pair d, d + k, n]ᵥ ↔ p ∈ 𝓛.Axiom) by
    specialize this p.depth 0 n p rfl (by rfl)
    simp at this; rw [Formula.depthPR_eval, this]
  intros d k l p h₁ h₂
  constructor
  · subst h₁
    induction' h₁ : Encodable.encode p using Nat.strong_induction_on with m ih generalizing d k p
    subst h₁
    rw [←h, covrec_eval, h]
    simp [Fin.exists_fin_succ]
    rintro (h | h | h | h | h | h | h | h | h | h | h | h)
    · simp [isFormulaPR_eval_pos_iff] at h
      rcases h with ⟨_, _, _, _, ⟨p, rfl⟩, ⟨q, rfl⟩, h⟩
      simp at h; subst h
      exact .imp_self
    · simp [Fin.ofNat_succ 6, Fin.forall_fin_succ, isFormulaPR_eval_pos_iff] at h
      rcases h with ⟨_, _, _, _, _, _, ⟨p, rfl⟩, ⟨q, rfl⟩, ⟨r, rfl⟩, h⟩
      simp at h; subst h
      exact .imp_distrib
    · simp [isFormulaPR_eval_pos_iff] at h
      rcases h with ⟨_, _, _, _, ⟨p, rfl⟩, ⟨q, rfl⟩, h⟩
      simp at h; subst h
      exact .transpose
    · simp [isTermPR_eval_pos_iff, isFormulaPR_eval_pos_iff] at h
      rcases h with ⟨_, _, _, _, ⟨p, rfl⟩, ⟨t, rfl⟩, h⟩
      simp [Formula.substSinglePR_eval] at h; subst h
      exact .forall_elim
    · simp [isFormulaPR_eval_pos_iff] at h
      rcases h with ⟨_, _, ⟨p, rfl⟩, h⟩
      simp [Formula.shiftPR_eval] at h; subst h
      exact .forall_self
    · simp [isFormulaPR_eval_pos_iff] at h
      rcases h with ⟨_, _, _, _, ⟨p, rfl⟩, ⟨q, rfl⟩, h⟩
      simp at h; subst h
      exact .forall_imp
    · simp [isTermPR_eval_pos_iff] at h
      rcases h with ⟨_, _, ⟨t, rfl⟩, h⟩
      simp at h; subst h
      exact .eq_refl
    · simp [isTermPR_eval_pos_iff] at h
      rcases h with ⟨_, _, _, _, ⟨t₁, rfl⟩, ⟨t₂, rfl⟩, h⟩
      simp at h; subst h
      exact .eq_symm
    · simp [Fin.ofNat_succ 6, Fin.forall_fin_succ, isTermPR_eval_pos_iff] at h
      rcases h with ⟨_, _, _, _, _, _, ⟨t₁, rfl⟩, ⟨t₂, rfl⟩, ⟨t₃, rfl⟩, h⟩
      simp at h; subst h
      exact .eq_trans
    · simp [Fin.ofNat_succ 6, Fin.ofNat_succ 7, Fin.forall_fin_succ, isFuncPR_eval_pos_iff, isvec_eval_pos_iff] at h
      rcases h with ⟨m, _, _, _, _, _, _, _, ⟨f, rfl⟩, ⟨_, rfl⟩, h', ⟨_, rfl⟩, h'', h⟩
      simp [vmap_eval, vand_eval_pos_iff, isTermPR_eval_pos_iff] at h' h''
      choose v₁ h' using h'
      choose v₂ h'' using h''
      simp [funext h', funext h'', vmk_eval, vget_eval] at h
      simp [←Vec.encode_eq] at h; subst h
      exact .eq_congr_func
    · simp [Fin.ofNat_succ 6, Fin.ofNat_succ 7, Fin.ofNat_succ 8, Fin.forall_fin_succ, isRelPR_eval_pos_iff, isvec_eval_pos_iff] at h
      rcases h with ⟨m, _, _, _, _, _, _, _, ⟨r, rfl⟩, ⟨_, rfl⟩, h', ⟨_, rfl⟩, h'', h⟩
      simp [vmap_eval, vand_eval_pos_iff, isTermPR_eval_pos_iff] at h' h''
      choose v₁ h' using h'
      choose v₂ h'' using h''
      simp [funext h', funext h'', vmk_eval, vget_eval] at h
      simp [←Vec.encode_eq] at h; subst h
      exact .eq_congr_rel
    · simp [Fin.ofNat_succ 6, Fin.ofNat_succ 7, Fin.ofNat_succ 8, Fin.ofNat_succ 9, isFormulaPR_eval_pos_iff] at h
      rcases h with ⟨_, _, ⟨p, rfl⟩, h, h'⟩
      simp at h'; subst h'
      cases' d with d <;> simp [Formula.depth] at h₂
      simp at h; rw [vget_eval'] at h
      · simp [Nat.add_right_comm] at h
        apply ih (Encodable.encode p) Formula.encode_lt_all d (k + 1) p h₂ rfl at h
        exact .all h
      · apply Nat.pair_lt_pair_left'
        · exact Formula.encode_lt_all
        · simp
  · intro h₃
    induction h₃ generalizing d k with (subst h₁; rw [←h, covrec_eval, h]; simp)
    | @imp_self _ p q =>
      exists 0; simp
      refine ⟨Encodable.encode p, ?_, Encodable.encode q, ?_, ?_⟩
      · exact Formula.encode_lt_imp_left
      · apply Formula.encode_lt_imp_right.trans'
        exact Formula.encode_lt_imp_left
      · simp [isFormulaPR_eval_pos_iff]
    | @imp_distrib _ p q r =>
      exists 1; simp
      refine ⟨Encodable.encode p, ?_, Encodable.encode q, ?_, Encodable.encode r, ?_, ?_⟩
      · apply Formula.encode_lt_imp_left.trans'
        exact Formula.encode_lt_imp_left
      · apply Formula.encode_lt_imp_left.trans'
        apply Formula.encode_lt_imp_right.trans'
        exact Formula.encode_lt_imp_left
      · apply Formula.encode_lt_imp_left.trans'
        apply Formula.encode_lt_imp_right.trans'
        exact Formula.encode_lt_imp_right
      · simp [Fin.forall_fin_succ, isFormulaPR_eval_pos_iff]
    | @transpose _ p q =>
      exists 2; simp
      refine ⟨Encodable.encode p, ?_, Encodable.encode q, ?_, ?_⟩
      · apply Formula.encode_lt_imp_right.trans'
        exact Formula.encode_lt_imp_right
      · apply Formula.encode_lt_imp_right.trans'
        exact Formula.encode_lt_imp_left
      · simp [isFormulaPR_eval_pos_iff]
    | @forall_elim _ p t =>
      rcases Formula.exists_encode_le_succ_subst_single (p := p) (t := t) with ⟨t', h₁, h₂⟩
      exists 3; simp
      refine ⟨Encodable.encode p, ?_, Encodable.encode t', ?_, ?_⟩
      · apply Formula.encode_lt_imp_left.trans'
        exact Formula.encode_lt_all
      · apply h₂.trans_lt
        simp
        apply Formula.encode_lt_imp_right
      · simp [isTermPR_eval_pos_iff, isFormulaPR_eval_pos_iff, Formula.substSinglePR_eval, h₁]
    | @forall_self _ p =>
      exists 4; simp
      refine ⟨Encodable.encode p, ?_, ?_⟩
      · exact Formula.encode_lt_imp_left
      · simp [isFormulaPR_eval_pos_iff, Formula.shiftPR_eval]
    | @forall_imp _ p q =>
      exists 5; simp
      refine ⟨Encodable.encode p, ?_, Encodable.encode q, ?_, ?_⟩
      · apply Formula.encode_lt_imp_left.trans'
        apply Formula.encode_lt_all.trans'
        exact Formula.encode_lt_imp_left
      · apply Formula.encode_lt_imp_left.trans'
        apply Formula.encode_lt_all.trans'
        exact Formula.encode_lt_imp_right
      · simp [isFormulaPR_eval_pos_iff]
    | @eq_refl _ t =>
      exists 6; simp
      refine ⟨Encodable.encode t, ?_, ?_⟩
      · exact Formula.encode_lt_eq_left
      · simp [isTermPR_eval_pos_iff]
    | @eq_symm _ t₁ t₂ =>
      exists 7; simp [Fin.ofNat_succ 6]
      refine ⟨Encodable.encode t₁, ?_, Encodable.encode t₂, ?_, ?_⟩
      · apply Formula.encode_lt_imp_left.trans'
        exact Formula.encode_lt_eq_left
      · apply Formula.encode_lt_imp_left.trans'
        exact Formula.encode_lt_eq_right
      · simp [isTermPR_eval_pos_iff]
    | @eq_trans _ t₁ t₂ t₃ =>
      exists 8; simp [Fin.ofNat_succ 6, Fin.ofNat_succ 7]
      refine ⟨Encodable.encode t₁, ?_, Encodable.encode t₂, ?_, Encodable.encode t₃, ?_, ?_⟩
      · apply Formula.encode_lt_imp_left.trans'
        exact Formula.encode_lt_eq_left
      · apply Formula.encode_lt_imp_left.trans'
        exact Formula.encode_lt_eq_right
      · apply Formula.encode_lt_imp_right.trans'
        apply Formula.encode_lt_imp_left.trans'
        exact Formula.encode_lt_eq_right
      · simp [Fin.forall_fin_succ, isTermPR_eval_pos_iff]
    | @eq_congr_func m _ v₁ v₂ f =>
      exists 9; simp [Fin.ofNat_succ 6, Fin.ofNat_succ 7, Fin.ofNat_succ 8]
      refine ⟨m, ?_, Encodable.encode f, ?_, Encodable.encode v₁, ?_, Encodable.encode v₂, ?_, ?_⟩
      · apply Formula.encode_lt_imp_right.trans'
        apply Formula.encode_lt_eq_left.trans'
        exact Term.encode_lt_func_m (𝓛 := 𝓛)
      · apply Formula.encode_lt_imp_right.trans'
        apply Formula.encode_lt_eq_left.trans'
        exact Term.encode_lt_func_f (𝓛 := 𝓛)
      · apply Formula.encode_lt_imp_right.trans'
        apply Formula.encode_lt_eq_left.trans'
        exact Term.encode_lt_func_v (𝓛 := 𝓛)
      · apply Formula.encode_lt_imp_right.trans'
        apply Formula.encode_lt_eq_right.trans'
        exact Term.encode_lt_func_v (𝓛 := 𝓛)
      · simp [Fin.forall_fin_succ, isFuncPR_eval_pos_iff, isTermPR_eval_pos_iff, isvec_eval_pos_iff, vmap_eval, vand_eval_pos_iff, Vec.encode_eq]
        simp [←Vec.encode_eq, vmk_eval]
        simp [Vec.encode_eq, vget_eval]
        simp [←Vec.encode_eq]
    | @eq_congr_rel m _ v₁ v₂ r =>
      exists 10; simp [Fin.ofNat_succ 6, Fin.ofNat_succ 7, Fin.ofNat_succ 8, Fin.ofNat_succ 9]
      refine ⟨m, ?_, Encodable.encode r, ?_, Encodable.encode v₁, ?_, Encodable.encode v₂, ?_, ?_⟩
      · apply Formula.encode_lt_imp_right.trans'
        apply Formula.encode_lt_imp_left.trans'
        exact Formula.encode_lt_rel_m (𝓛 := 𝓛)
      · apply Formula.encode_lt_imp_right.trans'
        apply Formula.encode_lt_imp_left.trans'
        exact Formula.encode_lt_rel_r (𝓛 := 𝓛)
      · apply Formula.encode_lt_imp_right.trans'
        apply Formula.encode_lt_imp_left.trans'
        exact Formula.encode_lt_rel_v (𝓛 := 𝓛)
      · apply Formula.encode_lt_imp_right.trans'
        apply Formula.encode_lt_imp_right.trans'
        exact Formula.encode_lt_rel_v (𝓛 := 𝓛)
      · simp [Fin.forall_fin_succ, isRelPR_eval_pos_iff, isTermPR_eval_pos_iff, isvec_eval_pos_iff, vmap_eval, vand_eval_pos_iff, Vec.encode_eq]
        simp [←Vec.encode_eq, vmk_eval]
        simp [Vec.encode_eq, vget_eval]
        simp [←Vec.encode_eq]
    | @all _ p _ ih =>
      exists 11; simp [Fin.ofNat_succ 6, Fin.ofNat_succ 7, Fin.ofNat_succ 8, Fin.ofNat_succ 9, Fin.ofNat_succ 10]
      refine ⟨Encodable.encode p, ?_, ?_⟩
      · exact Formula.encode_lt_all
      · simp [isFormulaPR_eval_pos_iff]
        cases' d with d <;> simp [Formula.depth] at h₂
        simp [Nat.add_right_comm]
        rw [vget_eval']
        · simp; exact ih d (k + 1) rfl h₂
        · apply Nat.pair_lt_pair_left'
          · exact Formula.encode_lt_all
          · simp

end

end FirstOrder.Language
