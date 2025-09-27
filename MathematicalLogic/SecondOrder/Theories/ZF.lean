import MathematicalLogic.ZFSet
import MathematicalLogic.SecondOrder.Semantics

abbrev InaccessibleCardinal := { κ : Cardinal // κ.IsInaccessible }

namespace SecondOrder.Language

private inductive zf.Func : ℕ → Type where
| empty : Func 0
| insert : Func 2
| sUnion : Func 1
| powerset : Func 1
| omega : Func 0

private inductive zf.Rel : ℕ → Type where
| mem : Rel 2

def zf : Language where
  Func := zf.Func
  Rel := zf.Rel

namespace zf

instance : EmptyCollection (zf.Term l) := ⟨.empty ⬝ᶠ []ᵥ⟩
instance : Insert (zf.Term l) (zf.Term l) := ⟨(.insert ⬝ᶠ [·, ·]ᵥ)⟩

def sUnion (t : zf.Term l) : zf.Term l := .sUnion ⬝ᶠ [t]ᵥ
scoped prefix:110 "⋃₀ " => sUnion

def powerset (t : zf.Term l) : zf.Term l := .powerset ⬝ᶠ [t]ᵥ
scoped prefix:100 "𝓟" => powerset

def omega : zf.Term l := .omega ⬝ᶠ []ᵥ
scoped notation "ω" => omega

def mem (t₁ t₂ : zf.Term l) : zf.Formula l := .mem ⬝ʳ [t₁, t₂]ᵥ
scoped infix:60 " ∈' " => mem

def globalChoice : zf.Sentence := ∃ᶠ[1] (∀' (∃' (#0 ∈' #1) ⇒ 1 ⬝ᶠᵛ [#0]ᵥ ∈' #0))

open ZFSet in
def V (κ : InaccessibleCardinal.{u}) : Type (u + 1) := (V_ κ.1.ord).toSet

namespace V

@[simp] theorem val_inj {x y : V κ} : x = y ↔ x.1 = y.1 := Subtype.val_inj.symm

open ZFSet in
instance : zf.HasStructure (V κ) where
  interpFunc
  | .empty, _ => ⟨∅, by
    simp [mem_vonNeumann, rank_empty]
    by_contra h
    simp at h
    simpa [h] using Cardinal.isSuccLimit_ord (le_of_lt κ.2.1)⟩
  | .insert, v => ⟨insert (v 0).1 (v 1).1, by
    simp [mem_vonNeumann, rank_insert]; constructor
    · apply (Cardinal.isSuccLimit_ord (le_of_lt κ.2.1)).succ_lt
      rw [←mem_vonNeumann]
      exact (v 0).2
    · rw [←mem_vonNeumann]; exact (v 1).2⟩
  | .sUnion, v => ⟨⋃₀ (v 0).1, by
    simp [mem_vonNeumann]
    apply lt_of_le_of_lt (rank_sUnion_le _)
    rw [←mem_vonNeumann]
    exact (v 0).2⟩
  | .powerset, v => ⟨ZFSet.powerset (v 0).1, by
    simp [mem_vonNeumann, rank_powerset]
    apply (Cardinal.isSuccLimit_ord (le_of_lt κ.2.1)).succ_lt
    rw [←mem_vonNeumann]
    exact (v 0).2⟩
  | .omega, v => ⟨.omega, by
    simp [mem_vonNeumann, rank_omega, Cardinal.lt_ord]; exact κ.2.1⟩
  interpRel
  | .mem, v => (v 0).1 ∈ (v 1).1

variable {t t₁ t₂ : zf.Term l} {ρ : Assignment (V κ) l}

@[simp] theorem interp_empty : (⟦ (∅ : zf.Term l) ⟧ₜ V κ, ρ).1 = ∅ := rfl
@[simp] theorem interp_insert : (⟦ insert t₁ t₂ ⟧ₜ V κ, ρ).1 = insert (⟦ t₁ ⟧ₜ V κ, ρ).1 (⟦ t₂ ⟧ₜ V κ, ρ).1 := rfl
@[simp] theorem interp_sUnion : (⟦ ⋃₀ t ⟧ₜ V κ, ρ).1 = ZFSet.sUnion (⟦ t ⟧ₜ V κ, ρ).1 := rfl
@[simp] theorem interp_powerset : (⟦ 𝓟 t ⟧ₜ V κ, ρ).1 = ZFSet.powerset (⟦ t ⟧ₜ V κ, ρ).1 := rfl
@[simp] theorem interp_omega : (⟦ ω ⟧ₜ V κ, ρ).1 = ZFSet.omega := rfl
@[simp] theorem satisfy_mem : V κ ⊨[ρ] t₁ ∈' t₂ ↔ (⟦ t₁ ⟧ₜ V κ, ρ).1 ∈ (⟦ t₂ ⟧ₜ V κ, ρ).1 := by rfl

end zf.V

namespace Theory

open zf

inductive ZF₂ : zf.Theory where
| ax_ext : ZF₂ (∀' (∀' ((∀' (#0 ∈' #2 ⇔ #0 ∈' #1)) ⇒ #1 ≐ #0)))
| ax_empty : ZF₂ (∀' (~ #0 ∈' ∅))
| ax_insert : ZF₂ (∀' (∀' (∀' (#0 ∈' insert #2 #1 ⇔ #0 ∈' #1 ⩒ #0 ≐ #2))))
| ax_union : ZF₂ (∀' (∀' (#0 ∈' ⋃₀ #1 ⇔ ∃' (#0 ∈' #2 ⩑ #1 ∈' #0))))
| ax_powerset : ZF₂ (∀' (∀' (#0 ∈' 𝓟 #1 ⇔ ∀' (#0 ∈' #1 ⇒ #0 ∈' #2))))
| ax_replacement : ZF₂ (∀' (∀ᶠ[1] (∃' (∀' (#0 ∈' #1 ⇔ ∃' (#0 ∈' #4 ⩑ #1 ≐ 3 ⬝ᶠᵛ [#0]ᵥ))))))
| ax_infinity : ZF₂ (∅ ∈' ω ⩑ ∀' (#0 ∈' ω ⇒ insert #0 #0 ∈' ω) ⩑ (∀' (∅ ∈' #0 ⩑ ∀' (#0 ∈' #1 ⇒ insert #0 #0 ∈' #1) ⇒ ∀' (#0 ∈' ω ⇒ #0 ∈' #1))))
| ax_regularity : ZF₂ (∀' (∃' (#0 ∈' #1) ⇒ ∃' (#0 ∈' #1 ⩑ ~ ∃' (#0 ∈' #2 ⩑ #0 ∈' #1))))

namespace ZF₂

open ZFSet in
instance : ZF₂.IsModel (zf.V κ) where
  satisfy_theory p h := by
    cases h with simp [Vec.eq_one, mem_omega_iff]
    | ax_ext =>
      intro x y h
      ext z
      constructor <;> intro h'
      · refine (h ⟨z, ?_⟩).mp h'; exact isTransitive_vonNeumann _ _ x.2 h'
      · refine (h ⟨z, ?_⟩).mpr h'; exact isTransitive_vonNeumann _ _ y.2 h'
    | ax_insert => intro _ _ _; exact or_comm
    | ax_union =>
      intro x y
      constructor
      · intro ⟨z, h₁, h₂⟩; exists ⟨z, isTransitive_vonNeumann _ _ x.2 h₁⟩
      · intro ⟨z, h₁, h₂⟩; exists z.1
    | ax_powerset =>
      intro x y
      constructor
      · intro h z; apply h
      · intro h z h'; exact h ⟨z, isTransitive_vonNeumann _ _ y.2 h'⟩ h'
    | ax_replacement =>
      intro x f
      classical
      let g : ZFSet → ZFSet := λ y => if h : y ∈ V_ κ.1.ord then (f [⟨y, h⟩]ᵥ).1 else ∅
      have : Definable₁ g := @Classical.allZFSetDefinable 1 _
      refine ⟨⟨image g x.1, ?_⟩, ?_⟩
      · simp; apply image_mem_V_of_inaccessible κ.2 x.2
        intro y h; simp [g,  isTransitive_vonNeumann _ _ x.2 h]
      · intro y
        constructor
        · simp; intro z h h'
          exists ⟨z, isTransitive_vonNeumann _ _ x.2 h⟩, h
          simp [←h', g, isTransitive_vonNeumann _ _ x.2 h]
        · intro ⟨z, h, h'⟩
          simp [h']
          exists z.1, h
          simp [g, isTransitive_vonNeumann _ _ x.2 h]
    | ax_infinity =>
      refine ⟨?_, ?_, ?_⟩
      · exists 0
      · intro x n h; simp [h]
        exists n + 1
      · intro x h₁ h₂ y n h; simp [h]; clear y h
        induction n with simp
        | zero => exact h₁
        | succ n ih =>
          refine h₂ ⟨ofNat n, ?_⟩ ih
          simp [mem_vonNeumann, rank_ofNat, Cardinal.lt_ord]
          exact (Cardinal.nat_lt_aleph0 n).trans κ.2.1
    | ax_regularity =>
      intro x y _
      have : x.1 ≠ ∅ := by simp [eq_empty]; exists y.1
      apply ZFSet.regularity at this
      rcases this with ⟨z, h₁, h₂⟩; simp [eq_empty] at h₂
      exists ⟨z, isTransitive_vonNeumann _ _ x.2 h₁⟩, h₁
      intro _ h₃ h₄; exact h₂ _ h₃ h₄

variable {M : Model.{u} ZF₂} {t t₁ t₂ : zf.Term l} {ρ : Assignment M l} {x y z : M}

open Classical

instance : Membership M M := ⟨λ y x => M.interpRel .mem [x, y]ᵥ⟩
@[simp] theorem satisfy_mem : M ⊨[ρ] t₁ ∈' t₂ ↔ ⟦ t₁ ⟧ₜ M, ρ ∈ ⟦ t₂ ⟧ₜ M, ρ := by
  simp [zf.mem, Membership.mem, Vec.eq_two]; rfl
@[ext] theorem ext : (∀ z, z ∈ x ↔ z ∈ y) → x = y := by
  have := M.satisfy_theory _ .ax_ext x y
  simp at this; exact this

instance : EmptyCollection M := ⟨M.interpFunc .empty []ᵥ⟩
@[simp] theorem interp_empty : ⟦ (∅ : zf.Term l) ⟧ₜ M, ρ = ∅ := by
  simp [EmptyCollection.emptyCollection, Vec.eq_nil]; rfl
instance : Inhabited M := ⟨∅⟩
@[simp] theorem mem_empty : ¬ x ∈ (∅ : M) := by
  have := M.satisfy_theory _ .ax_empty
  simp at this; apply this

def Nonempty (x : M) := ∃ y, y ∈ x
theorem nonempty_iff : Nonempty x ↔ x ≠ ∅ := by
  constructor
  · intro ⟨y, h₁⟩ h₂; simp [h₂, mem_empty] at h₁
  · intro h₁; by_contra h₂; simp [Nonempty] at h₂
    apply h₁; ext z; simp [h₂ z, mem_empty]

instance : Insert M M := ⟨(M.interpFunc .insert [·, ·]ᵥ)⟩
@[simp] theorem interp_insert : ⟦ insert t₁ t₂ ⟧ₜ M, ρ = insert (⟦ t₁ ⟧ₜ M, ρ) (⟦ t₂ ⟧ₜ M, ρ) := by
  simp [Insert.insert, Vec.eq_two]; rfl
@[simp] theorem mem_insert : z ∈ insert x y ↔ z ∈ y ∨ z = x := by
  have := M.satisfy_theory _ .ax_insert x y z
  simp at this; exact this

instance : Singleton M M := ⟨(insert · ∅)⟩
@[simp] theorem mem_singleton : y ∈ ({x} : M) ↔ y = x := by
  simp [Singleton.singleton]

def sUnion (x : M) : M := M.interpFunc .sUnion [x]ᵥ
@[simp] theorem interp_sUnion : ⟦ ⋃₀ t ⟧ₜ M, ρ = sUnion (⟦ t ⟧ₜ M, ρ) := by
  simp [zf.sUnion, sUnion, Vec.eq_one]; rfl
@[simp] theorem mem_sUnion : y ∈ sUnion x ↔ ∃ z, z ∈ x ∧ y ∈ z := by
  have := M.satisfy_theory _ .ax_union x y
  simp at this; exact this

instance : HasSubset M := ⟨(∀ ⦃z⦄, z ∈ · → z ∈ ·)⟩
theorem subset_iff : x ⊆ y ↔ ∀ z ∈ x, z ∈ y := by rfl
@[simp] theorem subset_refl : x ⊆ x := by simp [subset_iff]
theorem subset_antisymm : x ⊆ y → y ⊆ x → x = y := by
  intro h₁ h₂; ext z; constructor <;> apply_assumption
theorem subset_trans : x ⊆ y → y ⊆ z → x ⊆ z := by
  intros h₁ h₂ _ h; apply h₂; apply h₁; exact h
@[simp] theorem empty_subset : ∅ ⊆ x := by intro; simp
@[simp] theorem subset_insert : x ⊆ insert y x := by intro _ h; simp; exact Or.inl h

instance : HasSSubset M := ⟨λ x y => x ⊆ y ∧ x ≠ y⟩
theorem ssubset_iff : x ⊂ y ↔ x ⊆ y ∧ x ≠ y := by rfl
@[simp] theorem ssubset_irrefl : ¬ x ⊂ x := by simp [ssubset_iff]
theorem ssubset_trans : x ⊂ y → y ⊂ z → x ⊂ z := by
  intro ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
  exists subset_trans h₁ h₂
  by_contra h₃; subst h₃
  apply h₁'; exact subset_antisymm h₁ h₂

def powerset (x : M) : M := M.interpFunc .powerset [x]ᵥ
@[simp] theorem interp_powerset : ⟦ 𝓟 t ⟧ₜ M, ρ = powerset (⟦ t ⟧ₜ M, ρ) := by
  simp [zf.powerset, powerset, Vec.eq_one]; rfl
@[simp] theorem mem_power : y ∈ powerset x ↔ y ⊆ x := by
  have := M.satisfy_theory _ .ax_powerset x y
  simp at this; exact this

lemma exists_replace (x : M) (f : M → M) :
  ∃ (y : M), ∀ z, z ∈ y ↔ ∃ z' ∈ x, z = f z' := by
  have := M.satisfy_theory _ .ax_replacement x (f ·.head)
  simp at this; exact this

noncomputable def replace (x : M) (f : M → M) : M :=
  choose (exists_replace x f)
@[simp] theorem mem_replace : y ∈ replace x f ↔ ∃ z ∈ x, y = f z := by
  simp [replace]
  apply choose_spec (exists_replace x f)

noncomputable def sep (x : M) (p : M → Prop) : M :=
  sUnion (replace x λ y => if p y then {y} else ∅)
@[simp] theorem mem_sep : x ∈ sep y p ↔ x ∈ y ∧ p x := by
  simp [sep]; aesop

noncomputable instance : Inter M := ⟨λ x y => sep x (· ∈ y)⟩
@[simp] theorem mem_intersect : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := by
  simp [Inter.inter]

def omega (M : ZF₂.Model) : M := M.interpFunc .omega []ᵥ
@[simp] theorem interp_omega : ⟦ ω ⟧ₜ M, ρ = omega M := by simp [zf.omega, omega, Vec.eq_nil]; rfl

theorem empty_mem_omega : ∅ ∈ omega M := by
  have := M.satisfy_theory _ .ax_infinity
  simp at this; exact this.1

theorem succ_mem_omega : x ∈ omega M → insert x x ∈ omega M := by
  have := M.satisfy_theory _ .ax_infinity
  simp at this; apply this.2.1

theorem omega_minimal : ∅ ∈ x → (∀ y ∈ x, insert y y ∈ x) → omega M ⊆ x := by
  have := M.satisfy_theory _ .ax_infinity
  simp at this; apply this.2.2

def ofNat : ℕ → M
| 0 => ∅
| n + 1 => insert (ofNat n) (ofNat n)

theorem mem_omega_iff : x ∈ omega M ↔ ∃ n, x = ofNat n := by
  constructor
  · let y : M := sep (omega M) (λ x => ∃ n, x = ofNat n)
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

theorem regularity (x : M) : Nonempty x → ∃ y ∈ x, ¬ Nonempty (x ∩ y) := by
  have := M.satisfy_theory _ .ax_regularity x
  simp at this; simp [Nonempty]; exact this

theorem not_mem_self : ¬ x ∈ x := by
  have : Nonempty {x} := by simp [Nonempty]
  apply regularity at this
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

theorem ofNat_ssubset : n < m → @ofNat M n ⊂ ofNat m := by
  intro h
  induction h with
  | refl => exact ssubset_succ
  | step _ ih => exact ssubset_trans ih ssubset_succ

theorem ofNat_injective : Function.Injective (@ofNat M) := by
  intro n m h₁
  by_contra h₂
  apply lt_or_gt_of_ne at h₂
  rcases h₂ with h₂ | h₂ <;> apply @ofNat_ssubset M at h₂ <;> simp [h₁] at h₂

noncomputable def iUnionOmega (f : ℕ → M) : M :=
  sUnion (replace (omega M) (λ x => if h : x ∈ omega M then f (choose (mem_omega_iff.mp h)) else ∅))
@[simp] theorem mem_iUnionOmega : x ∈ iUnionOmega f ↔ ∃ n, x ∈ f n := by
  simp [iUnionOmega, mem_omega_iff]
  constructor
  · intro ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, h⟩
    simp at h; exact ⟨_, h⟩
  · intro ⟨n, h₁⟩
    exists f n; simp [h₁]
    exists ofNat n; simp; congr
    apply ofNat_injective
    exact choose_spec (⟨n, rfl⟩ : ∃ m, ofNat n = ofNat m)

def IsTransitive (x : M) := ∀ y ∈ x, y ⊆ x

def trclIter (x : M) : ℕ → M
| 0 => x
| n + 1 => sUnion (trclIter x n)

noncomputable def trcl (x : M) := iUnionOmega (trclIter x)

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

theorem mem_wf : @WellFounded M (· ∈ ·) := by
  rw [WellFounded.wellFounded_iff_has_min]
  intro s ⟨x, h₁⟩
  by_cases h₂ : Nonempty (sep (trcl x) s)
  · apply regularity at h₂; simp [Nonempty] at h₂
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

instance : IsWellFounded M (· ∈ ·) := ⟨mem_wf⟩
instance : WellFoundedRelation M := ⟨_, mem_wf⟩

/--
  Since GC (global choice) is true in the metalanguage (Lean), it is also true in any model of
  second-order ZF. In other words, GC (which implies AC) is no longer "independent" in second-order
  ZF.
  -/
theorem satisfy_global_choice : M ⊨ₛ globalChoice := by
  simp [globalChoice, Vec.eq_one]
  exists λ v => if h : ∃ y, y ∈ v 0 then choose h else ∅
  intro x y h
  have : ∃ y, y ∈ x := ⟨y, h⟩
  simp [this]
  exact choose_spec this

open Cardinal in
def card (x : M) : Cardinal.{u} := #{ y | y ∈ x }

theorem card_mono : x ⊆ y → card x ≤ card y := by
  intro h
  simp [card, Cardinal.le_def]
  refine ⟨λ ⟨z, h'⟩ => ⟨z, h h'⟩, ?_⟩
  intro ⟨z₁, h₁⟩ ⟨z₂, h₂⟩; simp

theorem card_powerset : card (powerset x) = 2 ^ card x := by
  rw [card, card, ←Cardinal.mk_powerset, Cardinal.eq]
  simp [Set.powerset]
  refine ⟨
    λ ⟨y, h⟩ => ⟨{ z | z ∈ y }, by simp; exact h⟩,
    λ ⟨s, h⟩ => ⟨sep x (· ∈ s), by intro z; simp; intro _ h'; exact h h'⟩,
    ?_, ?_⟩
  · intro ⟨y, h⟩; ext z; simp; apply h
  · intro ⟨s, h⟩; ext y; simp; apply h

theorem card_omega : card (omega M) = Cardinal.aleph0 := by
  rw [card, Cardinal.aleph0, ←Cardinal.mk_uLift, Cardinal.eq]
  refine ⟨
    λ ⟨x, h⟩ => ⟨choose (by simp [mem_omega_iff] at h; exact h)⟩,
    λ ⟨n⟩ => ⟨ofNat n, by simp [mem_omega_iff]⟩,
    ?_, ?_⟩
  · intro ⟨x, h⟩; simp [mem_omega_iff] at h
    rcases h with ⟨n, h⟩; subst h
    simp; symm; exact choose_spec (⟨n, rfl⟩ : ∃ m, ofNat n = ofNat m)
  · intro ⟨n⟩; simp
    apply ofNat_injective
    symm; exact choose_spec (⟨n, rfl⟩ : ∃ m, ofNat n = ofNat m)

theorem card_iUnion_ge_iSup : card (sUnion (replace x f)) ≥ iSup λ y : {y // y ∈ x} => card (f y) := by
  apply ciSup_le'
  intro ⟨y, h⟩
  apply card_mono
  intro z h'; aesop

noncomputable def kappa (M : Model.{u} ZF₂) : Cardinal.{u} := iSup (@card M)

theorem card_lt_kappa : card x < kappa M := by
  apply lt_of_lt_of_le (Cardinal.cantor _)
  rw [←card_powerset]
  apply le_ciSup (Cardinal.bddAbove_range _)

theorem exists_of_card_lt_kappa : c < kappa M → ∃ (x : M), c = card x := by
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

theorem kappa_gt_aleph0 : Cardinal.aleph0 < kappa M := by
  rw [←card_omega]; exact card_lt_kappa

theorem kappa_strong_limit : (kappa M).IsStrongLimit := by
  constructor
  · exact ne_zero_of_lt kappa_gt_aleph0
  · intro c h
    apply exists_of_card_lt_kappa at h; rcases h with ⟨x, h⟩
    subst h; rw [←card_powerset]
    exact card_lt_kappa

theorem kappa_regular : (kappa M).IsRegular := by
  constructor
  · exact kappa_gt_aleph0.le
  · by_contra h; simp at h
    apply exists_of_card_lt_kappa at h; rcases h with ⟨x, h⟩
    rcases Ordinal.exists_lsub_cof (kappa M).ord with ⟨ι, f, h₁, h₂⟩
    rw [h, card, Cardinal.eq] at h₂; rcases h₂ with ⟨e⟩; simp at e
    have : Set.range f = Set.range λ y : { y // y ∈ x } => f (e.symm y) := by
      ext o; simp; constructor
      · intro ⟨i, h₁⟩; exists e i, (e i).2; simp [h₁]
      · intro ⟨y, h₁, h₂⟩; exists e.symm ⟨y, h₁⟩
    rw [Ordinal.lsub_eq_of_range_eq this] at h₁
    have : ∀ y h, ∃ (z : M), f (e.symm ⟨y, h⟩) < (card z).ord := by
      intro y h
      have := Ordinal.lt_lsub (λ y => f (e.symm y)) ⟨y, h⟩
      rw [h₁, Cardinal.lt_ord] at this
      apply kappa_strong_limit.2 at this
      rcases exists_of_card_lt_kappa this with ⟨z, h⟩
      exists z; rw [Cardinal.lt_ord, ←h]; apply Cardinal.cantor
    choose! g h₂ using this
    have h₃ : Ordinal.lsub (λ y => f (e.symm y)) ≤ (iSup λ y : {y // y ∈ x} => card (g y)).ord := by
      rw [Ordinal.lsub_le_iff]
      intro ⟨y, h⟩
      apply (h₂ y h).trans_le
      simp; exact le_ciSup (Cardinal.bddAbove_range _) (⟨y, h⟩ : {y // y ∈ x})
    simp [h₁] at h₃
    apply le_trans' card_iUnion_ge_iSup at h₃
    exact not_le_of_gt card_lt_kappa h₃

theorem kappa_inaccessible : (kappa M).IsInaccessible :=
  ⟨kappa_gt_aleph0, kappa_regular.2, kappa_strong_limit.2⟩

noncomputable def rank : M → Ordinal.{u} := IsWellFounded.rank (· ∈ ·)

theorem rank_lt_kappa : rank x < (kappa M).ord := by
  induction' x using mem_wf.induction with x ih
  rw [rank, IsWellFounded.rank_eq]
  apply Cardinal.iSup_lt_ord_of_isRegular kappa_regular
  · apply card_lt_kappa
  · intro ⟨y, h⟩
    apply (Cardinal.isSuccLimit_ord (le_of_lt kappa_gt_aleph0)).succ_lt
    exact ih y h

noncomputable def toZFSet (x : M) : ZFSet.{u} :=
  @ZFSet.range {y // y ∈ x} _ λ ⟨y, _⟩ => toZFSet y
termination_by x

theorem mem_toZFSet {y : ZFSet} : y ∈ toZFSet x ↔ ∃ z ∈ x, y = toZFSet z := by
  rw [toZFSet]; aesop

theorem toZFSet_injective : Function.Injective (@toZFSet M) := by
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
  nth_rw 1 [toZFSet]; simp
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

theorem toZFSet_empty : toZFSet (∅ : M) = ∅ := by
  ext; simp [mem_toZFSet]

theorem toZFSet_insert : toZFSet (insert x y) = insert (toZFSet x) (toZFSet y) := by
  ext; simp [mem_toZFSet]; aesop

theorem toZFSet_union : toZFSet (sUnion x) = ZFSet.sUnion (toZFSet x) := by
  ext; aesop (add simp mem_toZFSet)

theorem toZFSet_powerset : toZFSet (powerset x) = ZFSet.powerset (toZFSet x) := by
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

theorem toZFSet_nat : toZFSet (ofNat n : M) = ZFSet.ofNat n := by
  induction n with simp [ofNat]
  | zero => exact toZFSet_empty
  | succ _ ih => simp [toZFSet_insert, ih]

theorem toZFSet_omega : toZFSet (omega M) = ZFSet.omega := by
  ext; simp [mem_toZFSet, mem_omega_iff, ZFSet.mem_omega_iff]; aesop (add simp toZFSet_nat)

theorem rank_toZFSet : (toZFSet x).rank = rank x := by
  induction' x using mem_wf.induction with x ih
  apply le_antisymm
  · rw [ZFSet.rank_le_iff]
    intro y h; simp [mem_toZFSet] at h
    rcases h with ⟨y', h₁, h₂⟩; subst h₂
    rw [ih _ h₁]
    exact IsWellFounded.rank_lt_of_rel h₁
  · rw [rank, IsWellFounded.rank_eq]
    apply Ordinal.iSup_le
    intro ⟨y, h⟩
    simp; rw [←rank, ←ih _ h]
    apply ZFSet.rank_lt_of_mem
    simp [h]

open Cardinal ZFSet in
theorem toZFSet_surjective_V_kappa {x : ZFSet} :
  x ∈ V_ (kappa M).ord → ∃ (y : M), toZFSet y = x := by
  intro h₁
  induction' x using ZFSet.inductionOn with x ih
  choose! f h₂ using λ y h => ih y h (isTransitive_vonNeumann _ x h₁ h)
  apply card_lt_of_mem_V_inaccessible kappa_inaccessible at h₁
  rw [ZFSet.card] at h₁
  apply exists_of_card_lt_kappa at h₁
  rcases h₁ with ⟨x', h₁⟩
  rw [←ZFSet.card, ←lift_inj.{u,u+1}, card_eq, ←lift_id #x.toSet, card, lift_mk_eq.{u+1,u,u+1}] at h₁
  rcases h₁ with ⟨e⟩
  exists sUnion (replace x' λ z => if h : z ∈ x' then {f (e.symm ⟨z, h⟩)} else ∅)
  ext y; simp [mem_toZFSet]; constructor
  · rintro ⟨_, ⟨_, ⟨_, h₃, rfl⟩, h₄⟩, rfl⟩
    simp [h₃] at h₄; subst h₄
    rw [h₂ _ (Subtype.property _)]
    apply Subtype.property
  · intro h
    exists f y; simp [h₂ _ h]
    exists {f y}; simp
    exists e ⟨y, h⟩, (e _).2
    split_ifs with h' <;> try simp
    exfalso; exact h' (e _).2

theorem iso_V (M : Model.{u} ZF₂) :
  ∃ (κ : InaccessibleCardinal.{u}), _root_.Nonempty (M.toStructure ≃ᴹ .of (V κ)) := by
  refine ⟨⟨kappa M, ?_⟩, ⟨Equiv.ofBijective (λ x => ⟨toZFSet x, ?_⟩) ⟨?_, ?_⟩, ?_, ?_⟩⟩
  · exact kappa_inaccessible
  · simp [ZFSet.mem_vonNeumann, rank_toZFSet]; exact rank_lt_kappa
  · intro _ _ h; simp at h; rw [Subtype.mk_eq_mk] at h; exact toZFSet_injective h
  · intro ⟨x, h⟩; simp at h; simp [@Subtype.mk_eq_mk ZFSet]; exact toZFSet_surjective_V_kappa h
  · intro _ f v
    cases f with rw [←Subtype.val_inj]
    | empty => simp [Vec.eq_nil]; exact toZFSet_empty
    | insert => rw [Vec.eq_two (_ ∘ _), Vec.eq_two v]; exact toZFSet_insert
    | sUnion => rw [Vec.eq_one (_ ∘ _), Vec.eq_one v]; exact toZFSet_union
    | powerset => rw [Vec.eq_one (_ ∘ _), Vec.eq_one v]; exact toZFSet_powerset
    | omega => simp [Vec.eq_nil]; exact toZFSet_omega
  · intro _ r v
    cases r with
    | mem => rw [Vec.eq_two (_ ∘ _), Vec.eq_two v]; exact toZFSet_mem.symm

end SecondOrder.Language.Theory.ZF₂
