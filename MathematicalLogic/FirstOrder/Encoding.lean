import MathematicalLogic.FirstOrder.Proof

namespace FirstOrder.Language

variable {𝓛 : Language}

section

variable [∀ n, Encodable (𝓛.Func n)]

def Term.encode : 𝓛.Term n → ℕ
| #x => 2 * x
| func (m := m) f v => 2 * m.pair ((Encodable.encode f).pair (Vec.paired λ i => (v i).encode)) + 1

mutual
def Term.decode (n k : ℕ) : Option (𝓛.Term n) :=
  if k.bodd then do
    let m := k.div2.unpair.1
    match @Encodable.decode (𝓛.Func m) _ k.div2.unpair.2.unpair.1 with
    | some f => do
      let v ← decodeVec n k.div2.unpair.2.unpair.2 m
      some (f ⬝ₜ v)
    | _ => none
  else
    if h : k.div2 < n then
      some #⟨_, h⟩
    else none
termination_by (k, 0)
decreasing_by
  simp_wf; simp [Prod.lex_def]
  apply Nat.lt_of_le_of_lt (Nat.unpair_right_le _)
  apply Nat.lt_of_le_of_lt (Nat.unpair_right_le _)
  apply Nat.binaryRec_decreasing
  intro h; subst h; contradiction

def Term.decodeVec (n k : ℕ) : (m : ℕ) → Option (Vec (𝓛.Term n) m)
| 0 => if k = 0 then some []ᵥ else none
| m + 1 => do
  let t ← decode n k.unpair.1
  let v ← decodeVec n k.unpair.2 m
  some (t ∷ᵥ v)
termination_by m => (k, m)
decreasing_by
  all_goals simp_wf; simp [Prod.lex_def]
  · exact Nat.lt_or_eq_of_le (Nat.unpair_left_le k)
  · exact Nat.lt_or_eq_of_le (Nat.unpair_right_le k)
end

theorem Term.encode_decode {t : 𝓛.Term n} : decode n t.encode = some t := by
  induction t with simp [encode, decode, Nat.div2_val]
  | @func m f v ih =>
    rw [Nat.div2_val, Nat.mul_add_div]
    · simp; rw [Nat.unpair_pair]; simp [Option.bind_eq_some]; clear f
      induction m with simp [decodeVec, Vec.paired]
      | zero => simp [Vec.eq_nil]
      | succ m ih' =>
        simp [Vec.head, Vec.tail, ih, Function.comp]
        rw [ih']
        · simp; nth_rw 3 [Vec.eq_cons v]; rfl
        · intro; apply ih
    · simp

instance : Encodable (𝓛.Term n) where
  encode := Term.encode
  decode := Term.decode n
  encodek _ := Term.encode_decode

@[simp] theorem Term.encode_var : Encodable.encode (#x : 𝓛.Term n) = 2 * x := rfl
@[simp] theorem Term.encode_func {v : Vec (𝓛.Term n) m} :
  Encodable.encode (f ⬝ₜ v) = 2 * m.pair ((Encodable.encode f).pair (Encodable.encode v)) + 1 := rfl

variable [∀ n, Encodable (𝓛.Rel n)]

def Formula.encode : 𝓛.Formula n → ℕ
| rel (m := m) r v => 4 * m.pair ((Encodable.encode r).pair (Vec.paired λ i => (v i).encode)) + 1
| t₁ ≐ t₂ => 4 * Nat.pair t₁.encode t₂.encode + 2
| ⊥ => 0
| p ⇒ q => 4 * Nat.pair p.encode q.encode + 3
| ∀' p => 4 * p.encode + 4

def Formula.decode (n k : ℕ) : Option (𝓛.Formula n) :=
  match k with
  | 0 => some ⊥
  | k + 1 =>
    match h : k % 4 with
    | 0 =>
      let m := (k / 4).unpair.1
      match @Encodable.decode (𝓛.Rel m) _ (k / 4).unpair.2.unpair.1 with
      | some r => do
        let v ← Term.decodeVec n (k / 4).unpair.2.unpair.2 m
        some (r ⬝ᵣ v)
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

theorem Formula.encode_decode {p : 𝓛.Formula n} : decode n p.encode = some p := by
  induction p with simp [encode, decode]
  | @rel m _ r v =>
    rw [Nat.mul_mod_right 4]; simp
    rw [Nat.mul_div_right, Nat.unpair_pair]
    · simp [Option.bind_eq_some]; clear r
      induction m with simp [Term.decodeVec, Vec.paired]
      | zero => simp [Vec.eq_nil]
      | succ m ih =>
      simp [Vec.head, Vec.tail, Term.encode_decode, Function.comp, ih]
      nth_rw 3 [Vec.eq_cons v]; rfl
    · simp
  | eq t₁ t₂ =>
    rw [Nat.mul_add_mod]; simp [Nat.mul_add_div, Term.encode_decode]
  | imp p q ih₁ ih₂ =>
    rw [Nat.mul_add_mod]; simp [Nat.mul_add_div, ih₁, ih₂]
  | all p ih =>
    rw [Nat.mul_add_mod]; simp [Nat.mul_add_div, ih]

instance : Encodable (𝓛.Formula n) where
  encode := Formula.encode
  decode := Formula.decode n
  encodek _ := Formula.encode_decode

@[simp] theorem Formula.encode_rel {v : Vec (𝓛.Term n) m} :
  Encodable.encode (r ⬝ᵣ v) = 4 * m.pair ((Encodable.encode r).pair (Encodable.encode v)) + 1 := rfl
@[simp] theorem Formula.encode_eq {t₁ t₂ : 𝓛.Term n} :
  Encodable.encode (t₁ ≐ t₂) = 4 * (Encodable.encode t₁).pair (Encodable.encode t₂) + 2 := rfl
@[simp] theorem Formula.encode_false :
  Encodable.encode (⊥ : 𝓛.Formula n) = 0 := rfl
@[simp] theorem Formula.encode_imp {p q : 𝓛.Formula n} :
  Encodable.encode (p ⇒ q) = 4 * (Encodable.encode p).pair (Encodable.encode q) + 3 := rfl
@[simp] theorem Formula.encode_all {p : 𝓛.Formula (n + 1)} :
  Encodable.encode (∀' p) = 4 * Encodable.encode p + 4 := rfl

lemma Formula.encode_lt_imp_left {p q : 𝓛.Formula n} : Encodable.encode p < Encodable.encode (p ⇒ q) := by
  simp [Nat.lt_succ]
  apply le_trans' (Nat.le_add_right _ _)
  apply le_trans' (Nat.le_mul_of_pos_left _ (by simp))
  apply Nat.left_le_pair

lemma Formula.encode_lt_imp_right {p q : 𝓛.Formula n} : Encodable.encode q < Encodable.encode (p ⇒ q) := by
  simp [encode, Nat.lt_succ]
  apply le_trans' (Nat.le_add_right _ _)
  apply le_trans' (Nat.le_mul_of_pos_left _ (by simp))
  apply Nat.right_le_pair

end

section
variable [∀ n, Countable (𝓛.Func n)] [∀ n, Countable (𝓛.Rel n)]
noncomputable scoped instance : Encodable (𝓛.Func n) := Encodable.ofCountable _
noncomputable scoped instance : Encodable (𝓛.Rel n) := Encodable.ofCountable _
instance : Countable (𝓛.Term n) := inferInstance
instance : Countable (𝓛.Formula n) := inferInstance
end

end FirstOrder.Language
