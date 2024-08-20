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
| extensionality : ZF₂ (∀' (∀' ((∀' (#0 ∈' #2 ⇔ #0 ∈' #1)) ⇒ #1 ≐ #0)))
| emptyset : ZF₂ (∀' (~ #0 ∈' ∅))
| insertion : ZF₂ (∀' (∀' (∀' (#0 ∈' insert #2 #1 ⇔ #0 ∈' #1 ⩒ #0 ≐ #2))))
| union : ZF₂ (∀' (∀' (#0 ∈' ⋃₀ #1 ⇔ ∃' (#0 ∈' #2 ⩑ #1 ∈' #0))))
| powerset : ZF₂ (∀' (∀' (#0 ∈' 𝓟 #1 ⇔ ∀' (#0 ∈' #1 ⇒ #0 ∈' #2))))
| replacement : ZF₂ (∀' (∀ᶠ 1 (∃' (∀' (#0 ∈' #1 ⇔ ∃' (#0 ∈' #4 ⩑ #1 ≐ 3 ⬝ᶠᵛ [#0]ᵥ))))))
| infinity : ZF₂ (∅ ∈' ω ⩑ ∀' (#0 ∈' ω ⇒ insert #0 #0 ∈' ω) ⩑ (∀' (∅ ∈' #0 ⩑ ∀' (#0 ∈' #1 ⇒ insert #0 #0 ∈' #1) ⇒ ∀' (#0 ∈' ω ⇒ #0 ∈' #1))))
| regularity : ZF₂ (∀' (∃' (#0 ∈' #1) ⇒ ∃' (#0 ∈' #1 ⩑ ~ ∃' (#0 ∈' #2 ⩑ #0 ∈' #1))))

namespace ZF₂

attribute [local simp] Structure.satisfy Structure.interpFormula Structure.interpTerm Structure.Assignment.cons

open ZFSet in
def 𝓥 (κ : Cardinal.{u}) (hκ : κ.IsInaccessible) : Model.{u+1} ZF₂ where
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
    | extensionality =>
      simp; intro x h₁ y h₂ h
      ext z; constructor
      · intro h'; refine (h _ ?_).left h'; exact V_transitive _ h₁ h'
      · intro h'; refine (h _ ?_).right h'; exact V_transitive _ h₂ h'
    | emptyset => simp
    | insertion => simp; aesop
    | union =>
      simp; intro x h₁ y _; constructor
      · intro z h₂ h₃; exists z, V_transitive _ h₁ h₂
      · aesop
    | powerset =>
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

variable {𝓜 : Model.{u} ZF₂} {x y z : 𝓜}

open Classical

instance : Membership 𝓜 𝓜 := ⟨(𝓜.interpRel .mem [·, ·]ᵥ)⟩

@[ext] theorem ext : (∀ z, z ∈ x ↔ z ∈ y) → x = y := by
  have := 𝓜.satisfy_theory _ .extensionality x y
  simp [Vec.eq_two, ←iff_iff_implies_and_implies] at this
  exact this

instance : EmptyCollection 𝓜 := ⟨𝓜.interpFunc .empty []ᵥ⟩
@[simp] theorem mem_empty : ¬ x ∈ (∅ : 𝓜) := by
  have := 𝓜.satisfy_theory _ .emptyset
  simp [Vec.eq_two, Vec.eq_nil] at this
  apply this
instance : Inhabited 𝓜 := ⟨∅⟩

def Nonempty (x : 𝓜) := ∃ y, y ∈ x
theorem nonempty_iff : Nonempty x ↔ x ≠ ∅ := by
  constructor
  · intro ⟨y, h₁⟩ h₂; simp [h₂, mem_empty] at h₁
  · intro h₁; by_contra h₂; simp [Nonempty] at h₂
    apply h₁; ext z; simp [h₂ z, mem_empty]

instance : Insert 𝓜 𝓜 := ⟨(𝓜.interpFunc .insert [·, ·]ᵥ)⟩
@[simp] theorem mem_insert : z ∈ insert x y ↔ z ∈ y ∨ z = x := by
  have := 𝓜.satisfy_theory _ .insertion x y z
  simp [Vec.eq_two, Vec.eq_nil, ←or_iff_not_imp_left, ←iff_iff_implies_and_implies] at this
  exact this

instance : Singleton 𝓜 𝓜 := ⟨(insert · ∅)⟩
@[simp] theorem mem_singleton : y ∈ ({x} : 𝓜) ↔ y = x := by
  simp [Singleton.singleton]

def sUnion (x : 𝓜) : 𝓜 := 𝓜.interpFunc .union [x]ᵥ
@[simp] theorem mem_sUnion : y ∈ sUnion x ↔ ∃ z, z ∈ x ∧ y ∈ z := by
  have := 𝓜.satisfy_theory _ .union x y
  simp [Vec.eq_two, Vec.eq_one] at this
  simp [iff_iff_implies_and_implies]
  exact this

instance : Union 𝓜 := ⟨(sUnion {·, ·})⟩
@[simp] theorem mem_union : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by
  simp [Union.union, or_comm]

instance : HasSubset 𝓜 := ⟨(∀ ⦃z⦄, z ∈ · → z ∈ ·)⟩
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

def power (x : 𝓜) : 𝓜 := 𝓜.interpFunc .powerset [x]ᵥ
@[simp] theorem mem_power : y ∈ power x ↔ y ⊆ x := by
  have := 𝓜.satisfy_theory _ .powerset x y
  simp [Vec.eq_two, Vec.eq_one] at this
  simp [Subset, iff_iff_implies_and_implies]
  exact this

lemma exists_replace (x : 𝓜) (f : 𝓜 → 𝓜) :
  ∃ (y : 𝓜), ∀ z, z ∈ y ↔ ∃ z' ∈ x, z = f z' := by
  have := 𝓜.satisfy_theory _ .replacement x (f ·.head)
  simp [Vec.head, Vec.eq_two] at this
  simp [iff_iff_implies_and_implies]
  exact this

noncomputable def replace (x : 𝓜) (f : ∀ y ∈ x, 𝓜) : 𝓜 :=
  sUnion (choose (exists_replace x λ y => if h : y ∈ x then {f y h} else ∅))
@[simp] theorem mem_replace : y ∈ replace x f ↔ ∃ z h, y = f z h := by
  have := choose_spec (exists_replace x λ y => if h : y ∈ x then {f y h} else ∅)
  simp [replace, this]
  constructor
  · aesop
  · intro ⟨z, h, h'⟩; exists {f z h}; aesop

noncomputable def sep (x : 𝓜) (p : 𝓜 → Prop) : 𝓜 :=
  sUnion (replace x λ y _ => if p y then {y} else ∅)
@[simp] theorem mem_sep : x ∈ sep y p ↔ x ∈ y ∧ p x := by
  simp [sep]; aesop

noncomputable instance : Inter 𝓜 := ⟨λ x y => sep x (· ∈ y)⟩
@[simp] theorem mem_intersect : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := by
  simp [Inter.inter]

def omega (𝓜 : ZF₂.Model) : 𝓜 := 𝓜.interpFunc .omega []ᵥ

theorem empty_mem_omega : ∅ ∈ omega 𝓜 := by
  have := 𝓜.satisfy_theory _ .infinity
  simp [Vec.eq_two, Vec.eq_nil] at this
  exact this.left

theorem succ_mem_omega : x ∈ omega 𝓜 → insert x x ∈ omega 𝓜 := by
  have := 𝓜.satisfy_theory _ .infinity
  simp [Vec.eq_two, Vec.eq_nil] at this
  exact this.right.left x

theorem omega_minimal : ∅ ∈ x → (∀ y ∈ x, insert y y ∈ x) → omega 𝓜 ⊆ x := by
  have := 𝓜.satisfy_theory _ .infinity
  simp [Vec.eq_two, Vec.eq_nil] at this
  exact this.right.right x

def ofNat : ℕ → 𝓜
| 0 => ∅
| n + 1 => insert (ofNat n) (ofNat n)

theorem mem_omega : x ∈ omega 𝓜 ↔ ∃ n, x = ofNat n := by
  constructor
  · let y : 𝓜 := sep (omega 𝓜) (λ x => ∃ n, x = ofNat n)
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

theorem regular (x : 𝓜) : Nonempty x → ∃ y ∈ x, ¬ Nonempty (x ∩ y) := by
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

noncomputable def iUnionOmega (f : ℕ → 𝓜) : 𝓜 :=
  sUnion (replace (omega 𝓜) (λ _ h => f (choose (mem_omega.1 h))))
@[simp] theorem mem_iUnionOmega : x ∈ iUnionOmega f ↔ ∃ n, x ∈ f n := by
  simp [iUnionOmega, mem_omega]
  constructor
  · aesop
  · intro ⟨n, h₁⟩
    exists f n; simp [h₁]
    exists ofNat n; simp; congr
    apply ofNat_injective
    exact choose_spec (⟨n, rfl⟩ : ∃ m, ofNat n = ofNat m)

def IsTransitive (x : 𝓜) := ∀ y ∈ x, y ⊆ x

def trclIter (x : 𝓜) : ℕ → 𝓜
| 0 => x
| n + 1 => sUnion (trclIter x n)

noncomputable def trcl (x : 𝓜) := iUnionOmega (trclIter x)

theorem trcl.self_subset : x ⊆ trcl x := by
  intro z h; simp [trcl]; exists 0

theorem trcl.transitive : IsTransitive (trcl x) := by
  intro y h₁ z h₂
  simp [trcl] at *
  rcases h₁ with ⟨n, h₁⟩
  exists n + 1; simp [trclIter]; exists y

theorem trcl.minimal : ∀ y ⊇ x, IsTransitive y → trcl x ⊆ y := by
  intro y h₁ h₂ z h₃
  simp [trcl] at h₃
  rcases h₃ with ⟨n, h₃⟩
  induction n generalizing z with simp [trclIter] at h₃
  | zero => exact h₁ h₃
  | succ n ih =>
    rcases h₃ with ⟨m, h₃, h₄⟩
    apply ih at h₃
    exact h₂ _ h₃ h₄

theorem mem_wf : @WellFounded 𝓜 (· ∈ ·) := by
  rw [WellFounded.wellFounded_iff_has_min]
  intro s ⟨x, h₁⟩
  by_cases h₂ : Nonempty (sep (trcl x) s)
  · apply regular at h₂; simp [Nonempty] at h₂
    rcases h₂ with ⟨y, ⟨h₂, h₃⟩, h₄⟩
    exists y, h₃
    intro z h₅ h₆
    apply h₄ z
    · exact trcl.transitive _ h₂ h₆
    · exact h₅
    · exact h₆
  · simp [Nonempty] at h₂
    exists x, h₁
    intro y h₃ h₄
    apply h₂ y
    · exact trcl.self_subset h₄
    · exact h₃

instance : WellFoundedRelation 𝓜 := ⟨_, mem_wf⟩

open Cardinal in
def card (x : 𝓜) : Cardinal.{u} := #{y | y ∈ x}

theorem card_mono : x ⊆ y → card x ≤ card y := by
  intro h
  simp [card, Cardinal.le_def]
  refine ⟨λ ⟨z, h'⟩ => ⟨z, h h'⟩, ?_⟩
  intro ⟨z₁, h₁⟩ ⟨z₂, h₂⟩; simp

theorem card_power : card (power x) = 2 ^ card x := by
  rw [card, card, ←Cardinal.mk_powerset, Cardinal.eq]
  simp [Set.powerset]
  refine ⟨
    λ ⟨y, h⟩ => ⟨{z | z ∈ y}, by simp; exact h⟩,
    λ ⟨s, h⟩ => ⟨sep x (· ∈ s), by intro z; simp; intro _ h'; exact h h'⟩,
    ?_, ?_⟩
  · intro ⟨y, h⟩; ext z; simp; apply h
  · intro ⟨s, h⟩; ext y; simp; apply h

theorem card_omega : card (omega 𝓜) = Cardinal.aleph0 := by
  rw [card, Cardinal.aleph0, ←Cardinal.mk_uLift, Cardinal.eq]
  refine ⟨
    λ ⟨x, h⟩ => ⟨choose (by simp [mem_omega] at h; exact h)⟩,
    λ ⟨n⟩ => ⟨ofNat n, by simp [mem_omega]⟩,
    ?_, ?_⟩
  · intro ⟨x, h⟩; simp [mem_omega] at h
    rcases h with ⟨n, h⟩; subst h
    simp; symm; exact choose_spec (⟨n, rfl⟩ : ∃ m, ofNat n = ofNat m)
  · intro ⟨n⟩; simp
    apply ofNat_injective
    symm; exact choose_spec (⟨n, rfl⟩ : ∃ m, ofNat n = ofNat m)

theorem card_iUnion_ge_iSup : card (sUnion (replace x f)) ≥ iSup λ y : {y // y ∈ x} => card (f y y.2) := by
  apply ciSup_le'
  intro ⟨y, h⟩
  apply card_mono
  intro z h'; aesop

noncomputable def kappa (𝓜 : Model.{u} ZF₂) : Cardinal.{u} := iSup (@card 𝓜)

theorem card_lt_kappa : card x < kappa 𝓜 := by
  apply lt_of_lt_of_le (Cardinal.cantor _)
  rw [←card_power]
  apply le_ciSup (Cardinal.bddAbove_range _)

theorem exists_of_card_lt_kappa : c < kappa 𝓜 → ∃ (x : 𝓜), c = card x := by
  intro h
  apply exists_lt_of_lt_ciSup at h
  rcases h with ⟨x, h⟩
  apply le_of_lt at h
  induction' c using Cardinal.inductionOn with α
  rw [card, Cardinal.le_def] at h
  rcases h with ⟨f⟩
  exists sep x (∃ a, · = f a)
  rw [card, Cardinal.eq]
  refine ⟨
    λ a => ⟨f a, by simp; exists (f a).2, a⟩,
    λ ⟨y, h⟩ => choose (by simp at h; exact h.2),
    ?_, ?_⟩
  · intro a; simp [Subtype.val_inj]
  · intro ⟨y, h⟩; simp at h
    rcases h with ⟨h₁, a, h₂⟩; subst h₂
    simp [Subtype.val_inj]

theorem kappa_gt_aleph0 : Cardinal.aleph0 < kappa 𝓜 := by
  rw [←card_omega]; exact card_lt_kappa

theorem kappa_strong_limit : (kappa 𝓜).IsStrongLimit := by
  constructor
  · exact ne_zero_of_lt kappa_gt_aleph0
  · intro c h
    apply exists_of_card_lt_kappa at h; rcases h with ⟨x, h⟩
    subst h; rw [←card_power]
    exact card_lt_kappa

theorem kappa_regular : (kappa 𝓜).IsRegular := by
  constructor
  · exact kappa_gt_aleph0.le
  · by_contra h; simp at h
    apply exists_of_card_lt_kappa at h; rcases h with ⟨x, h⟩
    rcases Ordinal.exists_lsub_cof (kappa 𝓜).ord with ⟨ι, f, h₁, h₂⟩
    rw [h, card, Cardinal.eq] at h₂; rcases h₂ with ⟨e⟩; simp at e
    have : Set.range f = Set.range λ y : { y // y ∈ x } => f (e.symm y) := by
      ext o; simp; constructor
      · intro ⟨i, h₁⟩; exists e i, (e i).2; simp [h₁]
      · intro ⟨y, h₁, h₂⟩; exists e.symm ⟨y, h₁⟩
    rw [Ordinal.lsub_eq_of_range_eq this] at h₁
    have : ∀ y h, ∃ (z : 𝓜), f (e.symm ⟨y, h⟩) < (card z).ord := by
      intro y h
      have := Ordinal.lt_lsub (λ y => f (e.symm y)) ⟨y, h⟩
      rw [h₁, Cardinal.lt_ord] at this
      apply kappa_strong_limit.2 at this
      rcases exists_of_card_lt_kappa this with ⟨z, h⟩
      exists z; rw [Cardinal.lt_ord, ←h]; apply Cardinal.cantor
    choose g h₂ using this
    have h₃ : Ordinal.lsub (λ y => f (e.symm y)) ≤ (iSup λ y : {y // y ∈ x} => card (g y y.2)).ord := by
      rw [Ordinal.lsub_le_iff]
      intro ⟨y, h⟩
      apply (h₂ y h).trans_le
      simp; exact le_ciSup (Cardinal.bddAbove_range _) (⟨y, h⟩ : {y // y ∈ x})
    simp [h₁] at h₃
    apply le_trans' card_iUnion_ge_iSup at h₃
    exact not_le_of_lt card_lt_kappa h₃

theorem kappa_inaccessible : (kappa 𝓜).IsInaccessible :=
  ⟨kappa_gt_aleph0, kappa_regular, kappa_strong_limit⟩

noncomputable def rank : 𝓜 → Ordinal.{u} := mem_wf.rank

theorem rank_lt_kappa : rank x < (kappa 𝓜).ord := by
  induction' x using mem_wf.induction with x ih
  rw [rank, mem_wf.rank_eq]
  apply Cardinal.sup_lt_ord_of_isRegular kappa_regular
  · apply card_lt_kappa
  · intro ⟨y, h⟩
    apply (Cardinal.ord_isLimit (le_of_lt kappa_gt_aleph0)).succ_lt
    exact ih y h

noncomputable def toZFSet (x : 𝓜) : ZFSet.{u} :=
  @ZFSet.range {y // y ∈ x} λ ⟨y, _⟩ => toZFSet y
termination_by x

theorem mem_toZFSet {y : ZFSet} : y ∈ toZFSet x ↔ ∃ z ∈ x, y = toZFSet z := by
  rw [toZFSet]; aesop

theorem toZFSet_injective : Function.Injective (@toZFSet 𝓜) := by
  intro x y h
  induction' x using mem_wf.induction with x ih generalizing y
  ext z
  constructor
  · intro h'
    have : toZFSet z ∈ toZFSet x := by simp [mem_toZFSet]; exists z
    rw [h] at this; simp [mem_toZFSet] at this
    rcases this with ⟨z', h₁, h₂⟩
    simpa [ih z h' h₂]
  · intro h'
    have : toZFSet z ∈ toZFSet y := by simp [mem_toZFSet]; exists z
    rw [←h] at this; simp [mem_toZFSet] at this
    rcases this with ⟨z', h₁, h₂⟩
    simpa [←ih z' h₁ h₂.symm]

@[simp] theorem toZFSet_mem : toZFSet x ∈ toZFSet y ↔ x ∈ y := by
  nth_rw 2 [toZFSet]; simp
  constructor
  · intro ⟨z, h₁, h₂⟩
    apply toZFSet_injective at h₂
    simpa [←h₂]
  · intro h; exists x

@[simp] theorem toZFSet_subset : toZFSet x ⊆ toZFSet y ↔ x ⊆ y := by
  constructor
  · intro h z h'
    rw [←toZFSet_mem] at h'
    apply h at h'
    simp at h'; exact h'
  · intro h z h'
    simp [mem_toZFSet] at h'
    rcases h' with ⟨z', h₁, h₂⟩; subst h₂
    simp; exact h h₁

theorem toZFSet_empty : toZFSet (∅ : 𝓜) = ∅ := by
  ext; simp [mem_toZFSet]

theorem toZFSet_insert : toZFSet (insert x y) = insert (toZFSet x) (toZFSet y) := by
  ext; simp [mem_toZFSet]; aesop

theorem toZFSet_union : toZFSet (sUnion x) = ZFSet.sUnion (toZFSet x) := by
  ext; aesop (add simp mem_toZFSet)

theorem toZFSet_power : toZFSet (power x) = ZFSet.powerset (toZFSet x) := by
  ext y; simp [mem_toZFSet]; constructor
  · aesop
  · intro h
    exists sep x λ z => toZFSet z ∈ y
    constructor
    · intro; aesop
    · ext z; simp [mem_toZFSet]; constructor
      · intro h'
        have := h h'
        simp [mem_toZFSet] at this
        rcases this with ⟨z', h₁, h₂⟩
        exists z'; aesop
      · aesop

theorem toZFSet_nat : toZFSet (ofNat n : 𝓜) = ZFSet.ofNat n := by
  induction n with simp [ofNat]
  | zero => exact toZFSet_empty
  | succ _ ih => simp [toZFSet_insert, ih]

theorem toZFSet_omega : toZFSet (omega 𝓜) = ZFSet.omega := by
  ext; simp [mem_toZFSet, mem_omega, ZFSet.mem_omega_iff]; aesop (add simp toZFSet_nat)

theorem rank_toZFSet : (toZFSet x).rank = rank x := by
  induction' x using mem_wf.induction with x ih
  apply le_antisymm
  · apply ZFSet.rank_le_of_mem_rank_lt
    intro y h; simp [mem_toZFSet] at h
    rcases h with ⟨y', h₁, h₂⟩; subst h₂
    rw [ih _ h₁]
    exact mem_wf.rank_lt_of_rel h₁
  · rw [rank, mem_wf.rank_eq]
    apply Ordinal.sup_le
    intro ⟨y, h⟩
    simp; rw [←rank, ←ih _ h]
    apply ZFSet.rank_lt_of_mem
    simp [h]

theorem toZFSet_surjective_V_kappa {x : ZFSet} :
  x ∈ ZFSet.V (kappa 𝓜).ord → ∃ (y : 𝓜), toZFSet y = x := by
  intro h₁
  induction' x using ZFSet.inductionOn with x ih
  choose f h₂ using λ y h => ih y h (ZFSet.V_transitive x h₁ h)
  apply ZFSet.card_lt_of_mem_V_inaccessible kappa_inaccessible at h₁
  rw [ZFSet.card] at h₁
  apply exists_of_card_lt_kappa at h₁
  rcases h₁ with ⟨x', h₁⟩
  rw [card, Cardinal.eq] at h₁; rcases h₁ with ⟨e⟩
  exists replace x' λ z h => x.familyOfBFamily f (e.symm ⟨z, h⟩)
  ext y; simp [mem_toZFSet]; constructor
  · intro ⟨_, ⟨_, h₁, h₂⟩, h₃⟩
    subst h₂ h₃
    simp [ZFSet.familyOfBFamily, h₂]
    exact (x.familyEquiv _).2
  · intro h
    exists f y h; simp [h₂]
    exists e (x.familyEquiv.symm ⟨y, h⟩), (e _).2
    simp [ZFSet.familyOfBFamily]

noncomputable def model_iso_𝓥 (𝓜 : Model.{u} ZF₂) :
  Σ' (κ : Cardinal.{u}) (hκ : κ.IsInaccessible), 𝓜.toStructure ≃ᴹ 𝓥 κ hκ :=
  ⟨kappa 𝓜, kappa_inaccessible, {
    toEquiv := Equiv.ofBijective
      (λ x => ⟨toZFSet x, by simp [ZFSet.mem_V_iff, rank_toZFSet]; exact rank_lt_kappa⟩)
      ⟨λ _ _ h => toZFSet_injective (Subtype.val_inj.2 h),
      λ ⟨x, h⟩ => by
        simp at h; simp_rw [@Subtype.mk_eq_mk ZFSet]
        exact toZFSet_surjective_V_kappa h⟩
    on_func :=
      λ
      | .empty, v => by simp [Vec.eq_nil, 𝓥]; apply toZFSet_empty
      | .insert, v => by rw [Vec.eq_two (_ ∘ _), Vec.eq_two v]; simp [𝓥]; apply toZFSet_insert
      | .union, v => by rw [Vec.eq_one (_ ∘ _), Vec.eq_one v]; simp [𝓥]; apply toZFSet_union
      | .powerset, v => by rw [Vec.eq_one (_ ∘ _), Vec.eq_one v]; simp [𝓥]; apply toZFSet_power
      | .omega, v => by simp [Vec.eq_nil, 𝓥]; apply toZFSet_omega
    on_rel :=
      λ
      | .mem, v => by rw [Vec.eq_two (_ ∘ _), Vec.eq_two v]; simp [𝓥]; rfl
  }⟩

theorem satisfy_global_choice : 𝓜 ⊨ₛ ZF₂.global_choice := by
  simp [Vec.eq_nil, Vec.eq_one, Vec.eq_two]; simp
  exists λ x => if h : ∃ y, y ∈ x.head then choose h else ∅
  intro x y h
  have : ∃ y, y ∈ x := ⟨y, h⟩
  simp [this]
  exact choose_spec this

end SecondOrder.Language.Theory.ZF₂
