import MathematicalLogic.FirstOrder.Syntax

namespace FirstOrder.Language

variable {L : Language}

section

variable [∀ n, Encodable (L.Func n)]

def Term.encode : L.Term n → ℕ
| #x => 2 * x
| func (m := m) f v => 2 * m.pair ((Encodable.encode f).pair (Vec.paired λ i => (v i).encode)) + 1

mutual
def Term.decode (n k : ℕ) : Option (L.Term n) :=
  if k.bodd then do
    let m := k.div2.unpair.1
    match @Encodable.decode (L.Func m) _ k.div2.unpair.2.unpair.1 with
    | some f => do
      let v ← decodeVec n k.div2.unpair.2.unpair.2 m
      some (f ⬝ᶠ v)
    | _ => none
  else
    if h : k.div2 < n then
      some #⟨_, h⟩
    else none
termination_by (k, 0)
decreasing_by
  simp [Prod.lex_def]
  apply Nat.lt_of_le_of_lt (Nat.unpair_right_le _)
  apply Nat.lt_of_le_of_lt (Nat.unpair_right_le _)
  apply Nat.binaryRec_decreasing
  intro h; subst h; contradiction

def Term.decodeVec (n k : ℕ) : (m : ℕ) → Option (Vec (L.Term n) m)
| 0 => if k = 0 then some []ᵥ else none
| m + 1 => do
  let t ← decode n k.unpair.1
  let v ← decodeVec n k.unpair.2 m
  some (t ∷ᵥ v)
termination_by m => (k, m)
decreasing_by
  all_goals simp_wf; simp [Prod.lex_def]
  · exact Nat.lt_or_eq_of_le (Nat.unpair_left_le _)
  · exact Nat.lt_or_eq_of_le (Nat.unpair_right_le _)
end

theorem Term.encode_decode {t : L.Term n} : decode n t.encode = some t := by
  induction t with simp [encode, decode, Nat.div2_val]
  | @func m f v ih =>
    rw [Nat.div2_val, Nat.mul_add_div]
    · simp; rw [Nat.unpair_pair]; simp [Option.bind_eq_some]; clear f
      induction m with simp [decodeVec, Vec.paired]
      | zero => simp [Vec.eq_nil]
      | succ m ih' =>
        simp [Vec.head, Vec.tail, ih, Function.comp_def]
        rw [ih']
        · simp; nth_rw 3 [Vec.eq_cons v]; rfl
        · intro; apply ih
    · simp

instance : Encodable (L.Term n) where
  encode := Term.encode
  decode := Term.decode n
  encodek _ := Term.encode_decode

theorem Term.encode_var : Encodable.encode (#x : L.Term n) = 2 * x := rfl
theorem Term.encode_func {v : Vec (L.Term n) m} :
  Encodable.encode (f ⬝ᶠ v) = 2 * m.pair ((Encodable.encode f).pair (Encodable.encode v)) + 1 := rfl
theorem Subst.encode_eq {σ : L.Subst n m} :
  Encodable.encode σ = Vec.paired λ i => Encodable.encode (σ i) := rfl
attribute [local simp] Term.encode_var Term.encode_func

theorem Term.encode_lt_func_m {v : Vec (L.Term n) m} :
  m < Encodable.encode (f ⬝ᶠ v) := by
  simp [Nat.lt_succ]
  apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
  apply Nat.left_le_pair

theorem Term.encode_lt_func_f {v : Vec (L.Term n) m} :
  Encodable.encode f < Encodable.encode (f ⬝ᶠ v) := by
  simp [Nat.lt_succ]
  apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
  apply (Nat.right_le_pair _ _).trans'
  apply Nat.left_le_pair

theorem Term.encode_lt_func_v {v : Vec (L.Term n) m} :
  Encodable.encode v < Encodable.encode (f ⬝ᶠ v) := by
  simp [Nat.lt_succ]
  apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
  apply (Nat.right_le_pair _ _).trans'
  apply Nat.right_le_pair

theorem Term.encode_le_subst {t : L.Term n} :
  x ∈ t.vars → Encodable.encode (σ x) ≤ Encodable.encode (t[σ]ₜ) := by
  intro h
  induction t with simp [vars] at h
  | var x => subst h; rfl
  | func f v ih =>
    rcases h with ⟨i, h⟩
    apply (ih i h).trans
    apply Nat.le_succ_of_le
    apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
    apply (Nat.right_le_pair _ _).trans'
    apply (Nat.right_le_pair _ _).trans'
    apply Vec.le_paired (i := i)

theorem Term.encode_subst_le_subst {t : L.Term n} :
  (∀ x, Encodable.encode (σ₁ x) ≤ Encodable.encode (σ₂ x)) →
  Encodable.encode (t[σ₁]ₜ) ≤ Encodable.encode (t[σ₂]ₜ) := by
  intro h
  induction t with simp
  | var x => apply h
  | func f v ih =>
    apply Nat.mul_le_mul_left
    apply Nat.pair_le_pair_right
    apply Nat.pair_le_pair_right
    apply Vec.paired_le_paired
    exact ih

theorem Term.encode_le_shift {t : L.Term n} : Encodable.encode t ≤ Encodable.encode (↑ₜt) := by
  conv => lhs; rw [←subst_id (t := t)]
  apply encode_subst_le_subst
  intro; simp [Nat.mul_le_mul_left]

variable [∀ n, Encodable (L.Rel n)]

def Formula.encode : L.Formula n → ℕ
| rel (m := m) r v => 4 * m.pair ((Encodable.encode r).pair (Vec.paired λ i => (v i).encode)) + 1
| t₁ ≐ t₂ => 4 * Nat.pair t₁.encode t₂.encode + 2
| ⊥ => 0
| p ⇒ q => 4 * Nat.pair p.encode q.encode + 3
| ∀' p => 4 * p.encode + 4

def Formula.decode (n k : ℕ) : Option (L.Formula n) :=
  match k with
  | 0 => some ⊥
  | k + 1 =>
    match h : k % 4 with
    | 0 =>
      let m := (k / 4).unpair.1
      match @Encodable.decode (L.Rel m) _ (k / 4).unpair.2.unpair.1 with
      | some r => do
        let v ← Term.decodeVec n (k / 4).unpair.2.unpair.2 m
        some (r ⬝ʳ v)
      | _ => none
    | 1 => do
      let t₁ ← Term.decode n (k / 4).unpair.1
      let t₂ ← Term.decode n (k / 4).unpair.2
      some (t₁ ≐ t₂)
    | 2 => do
      let p ← decode n (k / 4).unpair.1
      let q ← decode n (k / 4).unpair.2
      some (p ⇒ q)
    | 3 => do
      let p ← decode (n + 1) (k / 4)
      some (∀' p)
    | _ + 4 => none
termination_by k
decreasing_by
  all_goals simp_wf; simp [Nat.lt_succ]
  · apply le_trans (Nat.unpair_left_le _); apply Nat.div_le_self
  · apply le_trans (Nat.unpair_right_le _); apply Nat.div_le_self
  · apply Nat.div_le_self

theorem Formula.encode_decode {p : L.Formula n} : decode n p.encode = some p := by
  induction p with simp [encode, decode]
  | @rel m _ r v =>
    rw [Nat.mul_mod_right 4]; simp
    rw [Nat.mul_div_right, Nat.unpair_pair]
    · simp [Option.bind_eq_some]; clear r
      induction m with simp [Term.decodeVec, Vec.paired]
      | zero => simp [Vec.eq_nil]
      | succ m ih =>
      simp [Vec.head, Vec.tail, Term.encode_decode, Function.comp_def, ih]
      nth_rw 3 [Vec.eq_cons v]; rfl
    · simp
  | eq t₁ t₂ =>
    rw [Nat.mul_add_mod]; simp [Nat.mul_add_div, Term.encode_decode]
  | imp p q ih₁ ih₂ =>
    rw [Nat.mul_add_mod]; simp [Nat.mul_add_div, ih₁, ih₂]
  | all p ih =>
    rw [Nat.mul_add_mod]; simp [Nat.mul_add_div, ih]

instance : Encodable (L.Formula n) where
  encode := Formula.encode
  decode := Formula.decode n
  encodek _ := Formula.encode_decode

theorem Formula.encode_rel {v : Vec (L.Term n) m} :
  Encodable.encode (r ⬝ʳ v) = 4 * m.pair ((Encodable.encode r).pair (Encodable.encode v)) + 1 := rfl
theorem Formula.encode_eq {t₁ t₂ : L.Term n} :
  Encodable.encode (t₁ ≐ t₂) = 4 * (Encodable.encode t₁).pair (Encodable.encode t₂) + 2 := rfl
theorem Formula.encode_false :
  Encodable.encode (⊥ : L.Formula n) = 0 := rfl
theorem Formula.encode_imp {p q : L.Formula n} :
  Encodable.encode (p ⇒ q) = 4 * (Encodable.encode p).pair (Encodable.encode q) + 3 := rfl
theorem Formula.encode_all {p : L.Formula (n + 1)} :
  Encodable.encode (∀' p) = 4 * Encodable.encode p + 4 := rfl
attribute [local simp] Formula.encode_rel Formula.encode_eq Formula.encode_false Formula.encode_imp Formula.encode_all

theorem Formula.encode_lt_rel_m {v : Vec (L.Term n) m} :
  m < Encodable.encode (r ⬝ʳ v) := by
  simp [Nat.lt_succ]
  apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
  apply Nat.left_le_pair

theorem Formula.encode_lt_rel_r {v : Vec (L.Term n) m} :
  Encodable.encode r < Encodable.encode (r ⬝ʳ v) := by
  simp [Nat.lt_succ]
  apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
  apply (Nat.right_le_pair _ _).trans'
  apply Nat.left_le_pair

theorem Formula.encode_lt_rel_v {v : Vec (L.Term n) m} :
  Encodable.encode v < Encodable.encode (r ⬝ʳ v) := by
  simp [Nat.lt_succ]
  apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
  apply (Nat.right_le_pair _ _).trans'
  apply Nat.right_le_pair

theorem Formula.encode_lt_eq_left {t₁ t₂ : L.Term n} :
  Encodable.encode t₁ < Encodable.encode (t₁ ≐ t₂) := by
  simp [Nat.lt_succ]
  apply (Nat.le_add_right _ _).trans'
  apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
  apply Nat.left_le_pair

theorem Formula.encode_lt_eq_right {t₁ t₂ : L.Term n} :
  Encodable.encode t₂ < Encodable.encode (t₁ ≐ t₂) := by
  simp [Nat.lt_succ]
  apply (Nat.le_add_right _ _).trans'
  apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
  apply Nat.right_le_pair

theorem Formula.encode_lt_imp_left {p q : L.Formula n} :
  Encodable.encode p < Encodable.encode (p ⇒ q) := by
  simp [Nat.lt_succ]
  apply (Nat.le_add_right _ _).trans'
  apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
  apply Nat.left_le_pair

theorem Formula.encode_lt_imp_right {p q : L.Formula n} :
  Encodable.encode q < Encodable.encode (p ⇒ q) := by
  simp [Nat.lt_succ]
  apply (Nat.le_add_right _ _).trans'
  apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
  apply Nat.right_le_pair

theorem Formula.encode_lt_all {p : L.Formula (n + 1)} :
  Encodable.encode p < Encodable.encode (∀' p) := by
  simp [Formula.encode_all, Nat.lt_succ]
  apply (Nat.le_add_right _ _).trans'
  exact Nat.le_mul_of_pos_left _ (by simp)

theorem Formula.encode_le_alls {p : L.Formula n} :
  Encodable.encode p + n ≤ Encodable.encode (∀* p) := by
  induction n with simp [Formula.alls]
  | succ n ih => exact (Nat.add_lt_add_right encode_lt_all _).trans_le ih

theorem Formula.encode_le_alls_n {p : L.Formula n} :
  n ≤ Encodable.encode (∀* p) :=
  (Nat.le_add_left _ _).trans encode_le_alls

theorem Formula.encode_le_alls_p {p : L.Formula n} :
  Encodable.encode p ≤ Encodable.encode (∀* p) :=
  (Nat.le_add_right _ _).trans encode_le_alls

theorem Formula.encode_le_subst {p : L.Formula n} {σ : L.Subst n m} :
  x ∈ p.free → Encodable.encode (σ x) ≤ Encodable.encode (p[σ]ₚ) := by
  intro h
  induction p generalizing m with simp [free] at h <;> simp [encode]
  | rel r v =>
    rcases h with ⟨i, h⟩
    apply (Nat.le_add_right _ _).trans'
    apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
    apply (Nat.right_le_pair _ _).trans'
    apply (Nat.right_le_pair _ _).trans'
    apply le_trans' Vec.le_paired
    exact Term.encode_le_subst h
  | eq t₁ t₂ =>
    apply (Nat.le_add_right _ _).trans'
    apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
    cases h with
    | inl h => exact le_trans (Term.encode_le_subst h) (Nat.left_le_pair _ _)
    | inr h => exact le_trans (Term.encode_le_subst h) (Nat.right_le_pair _ _)
  | imp p q ih₁ ih₂ =>
    apply (Nat.le_add_right _ _).trans'
    apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
    cases h with
    | inl h => exact le_trans (ih₁ h) (Nat.left_le_pair _ _)
    | inr h => exact le_trans (ih₂ h) (Nat.right_le_pair _ _)
  | all p ih =>
    apply (Nat.le_add_right _ _).trans'
    apply (Nat.le_mul_of_pos_left _ (by simp)).trans'
    apply (ih h).trans'
    simp
    exact Term.encode_le_shift

theorem Formula.encode_le_subst_single {p : L.Formula (n + 1)} :
  0 ∈ p.free → Encodable.encode t ≤ Encodable.encode (p[↦ₛ t]ₚ) :=
  encode_le_subst (σ := ↦ₛ t)

-- workaround; should be fixed in the future using a `FinEncodable` class
class HasConstEncodeZero (L : Language) [Encodable L.Const] : Prop where
  hasConstEncodeZero : ∃ (r : L.Const), Encodable.encode r = 0

theorem Formula.exists_encode_le_succ_subst_single [HasConstEncodeZero L] {p : L.Formula (n + 1)} {t : L.Term n} :
  ∃ t', p[↦ₛ t]ₚ = p[↦ₛ t']ₚ ∧ Encodable.encode t' ≤ Encodable.encode (p[↦ₛ t]ₚ) + 1 := by
  by_cases h : 0 ∈ p.free
  · exists t, rfl; apply Nat.le_succ_of_le; exact encode_le_subst_single h
  · rcases HasConstEncodeZero.hasConstEncodeZero (L := L) with ⟨c, hc⟩
    exists c; constructor
    · apply subst_ext_free
      intro i h'
      cases i using Fin.cases with simp
      | zero => contradiction
    · simp [hc, Nat.pair]

end

section

variable [∀ n, Countable (L.Func n)] [∀ n, Countable (L.Rel n)]
noncomputable scoped instance : Encodable (L.Func n) := Encodable.ofCountable _
noncomputable scoped instance : Encodable (L.Rel n) := Encodable.ofCountable _
instance : Countable (L.Term n) := inferInstance
instance : Countable (L.Formula n) := inferInstance

end

end FirstOrder.Language
