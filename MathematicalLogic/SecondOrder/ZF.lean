import MathematicalLogic.ZFSet
import MathematicalLogic.SecondOrder.Semantics

namespace SecondOrder.Language

inductive ZF₂.Func : ℕ → Type where
| empty : Func 0
| insert : Func 2
| union : Func 1
| powerset : Func 1
| omega : Func 0

inductive ZF₂.Rel : ℕ → Type where
| mem : Rel 2

def ZF₂ : Language where
  Func := ZF₂.Func
  Rel := ZF₂.Rel

instance : EmptyCollection (ZF₂.Term Γ) := ⟨.empty ⬝ᶠ []ᵥ⟩
instance : Insert (ZF₂.Term Γ) (ZF₂.Term Γ) := ⟨(.insert ⬝ᶠ [·, ·]ᵥ)⟩
def Term.sUnion (t : ZF₂.Term Γ) : ZF₂.Term Γ := .union ⬝ᶠ [t]ᵥ
local prefix:110 "⋃₀ " => Term.sUnion
def Term.powerset (t : ZF₂.Term Γ) : ZF₂.Term Γ := .powerset ⬝ᶠ [t]ᵥ
local prefix:100 "𝓟" => Term.powerset
def Term.omega : ZF₂.Term Γ := .omega ⬝ᶠ []ᵥ
local notation "ω" => Term.omega
def Formula.mem (t₁ t₂ : ZF₂.Term Γ) : ZF₂.Formula Γ := .mem ⬝ʳ [t₁, t₂]ᵥ
local infix:60 " ∈' " => Formula.mem

def ZF₂.global_choice : ZF₂.Sentence := ∃ᶠ 1 (∀' (∃' (#0 ∈' #1) ⇒ 1 ⬝ᶠᵛ [#0]ᵥ ∈' #0))

namespace Theory

inductive ZF₂ : ZF₂.Theory where
| ext : ZF₂ (∀' (∀' ((∀' (#0 ∈' #2 ⇔ #0 ∈' #1)) ⇒ #1 ≐ #0)))
| mem_empty : ZF₂ (∀' (~ #0 ∈' ∅))
| mem_insert : ZF₂ (∀' (∀' (∀' (#0 ∈' insert #2 #1 ⇔ #0 ∈' #1 ⩒ #0 ≐ #2))))
| mem_union : ZF₂ (∀' (∀' (#0 ∈' ⋃₀ #1 ⇔ ∃' (#0 ∈' #2 ⩑ #1 ∈' #0))))
| mem_powerset : ZF₂ (∀' (∀' (#0 ∈' 𝓟 #1 ⇔ ∀' (#0 ∈' #1 ⇒ #0 ∈' #2))))
| replacement : ZF₂ (∀' (∀ᶠ 1 (∃' (∀' (#0 ∈' #1 ⇔ ∃' (#0 ∈' #4 ⩑ #1 ≐ 3 ⬝ᶠᵛ [#0]ᵥ))))))
| infinity : ZF₂ (∅ ∈' ω ⩑ ∀' (#0 ∈' ω ⇒ insert #0 #0 ∈' ω) ⩑ (∀' (∅ ∈' #0 ⩑ ∀' (#0 ∈' #1 ⇒ insert #0 #0 ∈' #1) ⇒ ∀' (#0 ∈' ω ⇒ #0 ∈' #1))))
| regularity : ZF₂ (∀' (∃' (#0 ∈' #1) ⇒ ∃' (#0 ∈' #1 ⩑ ~ ∃' (#0 ∈' #2 ⩑ #0 ∈' #1))))

namespace ZF₂

attribute [local simp] Structure.satisfy Structure.interpFormula Structure.interpTerm Structure.Assignment.cons
set_option maxHeartbeats 300000

open ZFSet in
def 𝓥 (κ : Cardinal) (hκ : κ.IsInaccessible) : ZF₂.Model where
  Dom := (V κ.ord).toSet
  interpFunc
  | .empty, _ => ⟨∅, by
    simp [mem_V_iff, rank_empty, Ordinal.one_le_iff_pos]
    exact (Cardinal.ord_isLimit (le_of_lt hκ.1)).pos⟩
  | .insert, v => ⟨Insert.insert (v 0).val (v 1), by
    simp [mem_V_iff, rank_insert]; constructor
    · apply (Cardinal.ord_isLimit (le_of_lt hκ.1)).succ_lt
      rw [←mem_V_iff]
      exact (v 0).property
    · rw [←mem_V_iff]; exact (v 1).property⟩
  | .union, v => ⟨⋃₀ (v 0), by
    simp [mem_V_iff]
    apply lt_of_le_of_lt rank_sUnion_le
    rw [←mem_V_iff]
    exact (v 0).property⟩
  | .powerset, v => ⟨ZFSet.powerset (v 0), by
    simp [mem_V_iff, rank_powerset]
    apply (Cardinal.ord_isLimit (le_of_lt hκ.1)).succ_lt
    rw [←mem_V_iff]
    exact (v 0).property⟩
  | .omega, v => ⟨omega, by
    simp [mem_V_iff, rank_omega, Cardinal.lt_ord]; exact hκ.1⟩
  interpRel
  | .mem, v => (v 0).val ∈ (v 1).val
  satisfy_theory p h := by
    cases h with simp only [Structure.satisfy, Structure.interpFormula, Structure.interpTerm, Structure.Assignment.cons]
    | ext =>
      simp; intro x h₁ y h₂ h
      ext z; constructor
      · intro h'; refine (h _ ?_).left h'; exact V_transitive _ h₁ h'
      · intro h'; refine (h _ ?_).right h'; exact V_transitive _ h₂ h'
    | mem_empty => simp
    | mem_insert => simp; aesop
    | mem_union =>
      simp; intro x h₁ y _; constructor
      · intro z h₂ h₃; exists z, V_transitive _ h₁ h₂
      · aesop
    | mem_powerset =>
      simp; intro x _ y h₁; constructor
      · aesop
      · intro h₂ z h₃; exact h₂ _ (V_transitive _ h₁ h₃) h₃
    | replacement =>
      intro ⟨x, h₁⟩ f
      rw [imp_false, not_forall]
      exists ⟨
        x.replace λ y h => f [⟨y, V_transitive _ h₁ h⟩]ᵥ,
        replace_mem_V_of_inaccessible hκ h₁ λ y h => Subtype.property _⟩
      rw [imp_false, not_not]
      intro ⟨y, h₂⟩
      rw [imp_false, Classical.not_imp]; constructor
      · intro h; simp [mem_replace] at h
        rcases h with ⟨z, h₃, h₄⟩
        rw [imp_false, not_forall]
        exists ⟨z, V_transitive _ h₁ h₃⟩
        rw [imp_false, not_not, imp_false, Classical.not_imp]; constructor
        · simp; exact h₃
        · rw [Vec.eq_one λ _ => _]
          simp [←Subtype.val_inj, h₄]
      · rw [imp_false, not_not]; intro h
        rw [imp_false, not_forall] at h
        rcases h with ⟨⟨z, h₃⟩, h⟩
        rw [Vec.eq_one λ _ => _] at h; simp [←Subtype.val_inj] at h
        simp [mem_replace]; exact ⟨z, h.left, h.right⟩
    | infinity =>
      rw [imp_false, Classical.not_imp]; constructor
      · rw [imp_false, Classical.not_imp]; constructor
        · exact omega_zero
        · rw [imp_false, not_not]; intro; apply omega_succ
      · rw [imp_false, not_not]; intro ⟨x, h₁⟩
        rw [imp_false, Classical.not_imp, imp_false, not_not]
        intro ⟨h₂, h₃⟩ ⟨y, h₄⟩ h₅; simp at *
        simp [mem_omega_iff] at h₅; rcases h₅ with ⟨n, h₅⟩; subst h₅; clear h₄
        induction n with
        | zero => exact h₂
        | succ n ih =>
          simp [ofNat_succ]; apply h₃
          · simp [mem_V_iff, rank_ofNat, Cardinal.lt_ord]
            exact (Cardinal.nat_lt_aleph0 n).trans hκ.1
          · exact ih
    | regularity =>
      simp; intro x h₁ y _ h₂
      have : x ≠ ∅ := by simp [eq_empty]; exists y
      apply ZFSet.regularity at this
      rcases this with ⟨z, h₃, h₄⟩
      exists z, V_transitive _ h₁ h₃, h₃
      intro _ _; simp [eq_empty] at h₄; apply h₄

variable {𝓜 : ZF₂.Model} {x y z : 𝓜}

instance : Membership 𝓜 𝓜 := ⟨(𝓜.interpRel .mem [·, ·]ᵥ)⟩

@[ext] theorem ext' : (∀ z, z ∈ x ↔ z ∈ y) → x = y := by
  have := 𝓜.satisfy_theory _ .ext x y
  simp [Vec.eq_two, ←iff_iff_implies_and_implies] at this
  exact this

instance : EmptyCollection 𝓜 := ⟨𝓜.interpFunc .empty []ᵥ⟩
@[simp] theorem mem_empty' : ¬ x ∈ (∅ : 𝓜) := by
  have := 𝓜.satisfy_theory _ .mem_empty
  simp [Vec.eq_two, Vec.eq_nil] at this
  apply this

def Nonempty (x : 𝓜) := ∃ y, y ∈ x
theorem nonempty_iff : Nonempty x ↔ x ≠ ∅ := by
  constructor
  · intro ⟨y, h₁⟩ h₂; simp [h₂, mem_empty] at h₁
  · intro h₁; by_contra h₂; simp [Nonempty] at h₂
    apply h₁; ext z; simp [h₂ z, mem_empty]

instance : Insert 𝓜 𝓜 := ⟨(𝓜.interpFunc .insert [·, ·]ᵥ)⟩
@[simp] theorem mem_insert' : x ∈ insert y z ↔ x ∈ z ∨ x = y := by
  have := 𝓜.satisfy_theory _ .mem_insert y z x
  simp [Vec.eq_two, Vec.eq_nil, ←or_iff_not_imp_left, ←iff_iff_implies_and_implies] at this
  exact this

instance : Singleton 𝓜 𝓜 := ⟨(insert · ∅)⟩
@[simp] theorem mem_singleton : x ∈ ({y} : 𝓜) ↔ x = y := by
  simp [Singleton.singleton]

def sUnion (x : 𝓜) : 𝓜 := 𝓜.interpFunc .union [x]ᵥ
@[simp] theorem mem_sUnion : x ∈ sUnion y ↔ ∃ z, z ∈ y ∧ x ∈ z := by
  have := 𝓜.satisfy_theory _ .mem_union y x
  simp [Vec.eq_two, Vec.eq_one] at this
  simp [iff_iff_implies_and_implies]
  exact this

instance : Union 𝓜 := ⟨(sUnion {·, ·})⟩
@[simp] theorem mem_union' : x ∈ y ∪ z ↔ x ∈ y ∨ x ∈ z := by
  simp [Union.union, or_comm]

instance : HasSubset 𝓜 := ⟨(∀ z, z ∈ · → z ∈ ·)⟩
theorem subset_iff : x ⊆ y ↔ ∀ z ∈ x, z ∈ y := by rfl
@[simp] theorem subset_refl : x ⊆ x := by simp [subset_iff]
theorem subset_antisymm : x ⊆ y → y ⊆ x → x = y := by
  intro h₁ h₂; ext z; constructor <;> apply_assumption
theorem subset_trans : x ⊆ y → y ⊆ z → x ⊆ z := by
  intros h₁ h₂ _ h; apply h₂; apply h₁; exact h
@[simp] theorem empty_subset : ∅ ⊆ x := by intro; simp
@[simp] theorem subset_insert : x ⊆ insert y x := by intro _ h; simp; exact Or.inl h

instance : HasSSubset 𝓜 := ⟨λ x y => x ⊆ y ∧ x ≠ y⟩
theorem ssubset_iff : x ⊂ y ↔ x ⊆ y ∧ x ≠ y := by rfl

@[simp] theorem ssubset_irrefl : ¬ x ⊂ x := by simp [ssubset_iff]
theorem ssubset_trans : x ⊂ y → y ⊂ z → x ⊂ z := by
  intro ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
  exists subset_trans h₁ h₂
  by_contra h₃; subst h₃
  apply h₁'; exact subset_antisymm h₁ h₂

def powerset (x : 𝓜) : 𝓜 := 𝓜.interpFunc .powerset [x]ᵥ
@[simp] theorem mem_powerset' : x ∈ powerset y ↔ x ⊆ y := by
  have := 𝓜.satisfy_theory _ .mem_powerset y x
  simp [Vec.eq_two, Vec.eq_one] at this
  simp [Subset, iff_iff_implies_and_implies]
  exact this

lemma exists_replacement (x : 𝓜) (f : 𝓜 → 𝓜) :
  ∃ (y : 𝓜), ∀ z, z ∈ y ↔ ∃ z' ∈ x, z = f z' := by
  have := 𝓜.satisfy_theory _ .replacement x (f ·.head)
  simp [Vec.head, Vec.eq_two] at this
  simp [iff_iff_implies_and_implies]
  exact this

noncomputable def replace (x : 𝓜) (f : 𝓜 → 𝓜) : 𝓜 :=
  Classical.choose (exists_replacement x f)
@[simp] theorem mem_replace : x ∈ replace y f ↔ ∃ z, z ∈ y ∧ x = f z :=
  Classical.choose_spec (exists_replacement y f) x

open Classical in
noncomputable def sep (x : 𝓜) (p : 𝓜 → Prop) : 𝓜 :=
  if h : ∃ y ∈ x, p y then replace x (λ z => if p z then z else choose h) else ∅
@[simp] theorem mem_sep : x ∈ sep y p ↔ x ∈ y ∧ p x := by
  simp [sep]
  by_cases h : ∃ z ∈ y, p z
  · simp [h]
    constructor
    · intro ⟨z, h₁, h₂⟩
      by_cases h' : p z
      · simp [h'] at h₂; subst h₂; simp [h₁, h']
      · simp [h'] at h₂
        have := Classical.choose_spec h
        rw [←h₂] at this; exact this
    · intro ⟨h₁, h₂⟩; exists x; simp [h₁, h₂]
  · simp [h]
    intro h₁ h₂
    exact h ⟨x, h₁, h₂⟩

noncomputable instance : Inter 𝓜 := ⟨λ x y => sep x (· ∈ y)⟩
@[simp] theorem mem_intersect : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := by
  simp [Inter.inter]

def omega : 𝓜 := 𝓜.interpFunc .omega []ᵥ

theorem empty_mem_omega : ∅ ∈ @omega 𝓜 := by
  have := 𝓜.satisfy_theory _ .infinity
  simp [Vec.eq_two, Vec.eq_nil] at this
  exact this.left

theorem succ_mem_omega : x ∈ @omega 𝓜 → insert x x ∈ omega := by
  have := 𝓜.satisfy_theory _ .infinity
  simp [Vec.eq_two, Vec.eq_nil] at this
  exact this.right.left x

theorem omega_minimal : ∅ ∈ x → (∀ y ∈ x, insert y y ∈ x) → @omega 𝓜 ⊆ x := by
  have := 𝓜.satisfy_theory _ .infinity
  simp [Vec.eq_two, Vec.eq_nil] at this
  exact this.right.right x

def ofNat : ℕ → 𝓜
| 0 => ∅
| n + 1 => insert (ofNat n) (ofNat n)

theorem mem_omega : x ∈ omega ↔ ∃ n, x = ofNat n := by
  constructor
  · let y : 𝓜 := sep omega (λ x => ∃ n, x = ofNat n)
    have h₁ : ∅ ∈ y := by simp [y, empty_mem_omega]; exists 0
    have h₂ : ∀ z ∈ y, insert z z ∈ y := by
      intro z h; simp [y] at h; rcases h with ⟨h₁, ⟨n, h₂⟩⟩; subst h₂
      simp [y, succ_mem_omega h₁]; exists (n + 1)
    intro h
    apply omega_minimal h₁ h₂ at h; simp [y] at h
    exact h.right
  · intro ⟨n, h⟩; subst h
    induction n with simp [ofNat]
    | zero => exact empty_mem_omega
    | succ _ ih => exact succ_mem_omega ih

theorem regular : Nonempty x → ∃ y ∈ x, ¬ Nonempty (x ∩ y) := by
  have := 𝓜.satisfy_theory _ .regularity x
  simp [Vec.eq_two, Vec.eq_nil] at this
  simp [Nonempty]
  exact this

theorem not_mem_self : ¬ x ∈ x := by
  have : Nonempty {x} := by simp [Nonempty]
  apply regular at this
  rcases this with ⟨y, h₁, h₂⟩
  simp at h₁; subst h₁
  simp [Nonempty] at h₂
  exact h₂

lemma ssubset_succ : x ⊂ insert x x := by
  simp [ssubset_iff]
  intro h
  have : x ∈ insert x x := by simp
  rw [←h] at this
  exact not_mem_self this

theorem ofNat_ssubset : n < m → @ofNat 𝓜 n ⊂ ofNat m := by
  intro h
  induction h with
  | refl => exact ssubset_succ
  | step _ ih => exact ssubset_trans ih ssubset_succ

theorem ofNat_injective : Function.Injective (@ofNat 𝓜) := by
  intro n m h₁
  by_contra h₂
  apply lt_or_gt_of_ne at h₂
  rcases h₂ with h₂ | h₂ <;> apply @ofNat_ssubset 𝓜 at h₂ <;> simp [h₁] at h₂

open Classical in
noncomputable def iUnionOmega (f : ℕ → 𝓜) : 𝓜 :=
  sUnion (replace omega (λ x => if h : ∃ n, x = ofNat n then f (Classical.choose h) else ∅))
@[simp] theorem mem_iUnionOmega : x ∈ iUnionOmega f ↔ ∃ n, x ∈ f n := by
  simp [iUnionOmega, mem_omega]
  constructor
  · intro ⟨_, ⟨_, ⟨⟨n, h₁⟩, h₂⟩⟩, h₃⟩
    subst h₁ h₂
    split at h₃
    next h => exact ⟨_, h₃⟩
    next => simp at h₃
  · intro ⟨n, h₁⟩
    exists f n
    constructor
    · exists ofNat n; simp; congr
      apply ofNat_injective
      exact Classical.choose_spec (⟨n, rfl⟩ : ∃ m, ofNat n = ofNat m)
    · exact h₁

def Transitive (x : 𝓜) := ∀ y ∈ x, y ⊆ x

theorem Transitive.nat : Transitive (@ofNat 𝓜 n) := by
  induction n with simp [ofNat]
  | zero => simp [Transitive]
  | succ _ ih =>
    intro x h; simp at h
    cases h with
    | inl h => apply ih at h; apply subset_trans h; simp
    | inr h => subst h; simp

def transIter (x : 𝓜) : ℕ → 𝓜
| 0 => x
| n + 1 => sUnion (transIter x n)

noncomputable def transClosure (x : 𝓜) := iUnionOmega (transIter x)

theorem transClosure.self_subset : x ⊆ transClosure x := by
  intro z h; simp [transClosure]; exists 0

theorem transClosure.transitive : Transitive (transClosure x) := by
  intro y h₁ z h₂
  simp [transClosure] at *
  rcases h₁ with ⟨n, h₁⟩
  exists n + 1; simp [transIter]; exists y

theorem transClosure.minimal : ∀ y ⊇ x, Transitive y → transClosure x ⊆ y := by
  intro y h₁ h₂ z h₃
  simp [transClosure] at h₃
  rcases h₃ with ⟨n, h₃⟩
  induction n generalizing z with simp [transIter] at h₃
  | zero => exact h₁ _ h₃
  | succ n ih =>
    rcases h₃ with ⟨m, h₃, h₄⟩
    apply ih at h₃
    exact h₂ _ h₃ _ h₄

theorem mem_wellfounded : @WellFounded 𝓜 (· ∈ ·) := by
  rw [WellFounded.wellFounded_iff_has_min]
  intro s ⟨x, h₁⟩
  by_cases h₂ : Nonempty (sep (transClosure x) s)
  · apply regular at h₂; simp [Nonempty] at h₂
    rcases h₂ with ⟨y, ⟨h₂, h₃⟩, h₄⟩
    exists y, h₃
    intro z h₅ h₆
    apply h₄ z
    · exact transClosure.transitive _ h₂ _ h₆
    · exact h₅
    · exact h₆
  · simp [Nonempty] at h₂
    exists x, h₁
    intro y h₃ h₄
    apply h₂ y
    · exact transClosure.self_subset _ h₄
    · exact h₃

open Classical in
theorem satisfy_global_choice : 𝓜 ⊨ₛ ZF₂.global_choice := by
  simp [Vec.eq_nil, Vec.eq_one, Vec.eq_two]; simp
  exists λ x => if h : ∃ y, y ∈ x.head then Classical.choose h else ∅
  intro x y h
  have : ∃ y, y ∈ x := ⟨y, h⟩
  simp [this]
  exact Classical.choose_spec this

end SecondOrder.Language.Theory.ZF₂
