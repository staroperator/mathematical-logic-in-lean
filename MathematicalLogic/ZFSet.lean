import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.ZFC.Ordinal

universe u v

namespace PSet

theorem mem_iff {x y : PSet} : x ∈ y ↔ ∃ b, Equiv x (y.Func b) := by rfl

noncomputable def rank : PSet.{u} → Ordinal.{u}
| ⟨_, A⟩ => Ordinal.sup λ i => have := Mem.mk A i; (A i).rank + 1

lemma rank_eq_of_equiv : (x y : PSet) → x.Equiv y → x.rank = y.rank
| ⟨_, A⟩, ⟨_, B⟩, h => by
  simp [rank]
  apply Ordinal.sup_eq_of_range_eq
  ext α; simp; constructor
  · intro ⟨i, h₁⟩
    rcases h.left i with ⟨j, h₂⟩
    exists j; rw [←h₁, rank_eq_of_equiv _ _ h₂]
  · intro ⟨j, h₁⟩
    rcases h.right j with ⟨i, h₂⟩
    exists i; rw [←h₁, rank_eq_of_equiv _ _ h₂]

theorem rank_lt_of_mem : {x y : PSet} → y ∈ x → y.rank < x.rank
| ⟨_, A⟩, y, h => by
  simp only [rank, Quotient.liftOn_mk, PSet.rank]
  rcases h with ⟨i, h⟩
  rw [PSet.rank_eq_of_equiv _ _ h]
  simp; rw [←Order.succ_le_iff]
  apply Ordinal.le_sup

theorem rank_le_of_mem_rank_lt : {x : PSet} → (∀ y ∈ x, y.rank < α) → x.rank ≤ α
| ⟨_, A⟩, h => by
  simp [rank]
  apply Ordinal.sup_le
  intro i
  rw [Order.succ_le_iff]
  apply h; apply Mem.mk

end PSet

namespace ZFSet

def ofNat (n : ℕ) := ZFSet.mk (.ofNat n)
@[simp] theorem ofNat_zero : ofNat 0 = ∅ := rfl
@[simp] theorem ofNat_succ : ofNat (n + 1) = insert (ofNat n) (ofNat n) := rfl

theorem mem_omega_iff : x ∈ omega ↔ ∃ n, x = ofNat n := by
  induction' x using Quotient.inductionOn with x
  simp [omega, PSet.omega]
  constructor
  · intro ⟨⟨n⟩, h⟩; simp at h; exists n; exact Quotient.sound h
  · intro ⟨_, h⟩; exact ⟨_, ZFSet.exact h⟩

section

local instance familySetoid (x : ZFSet) : Setoid x.out.Type := PSet.setoid.comap x.out.Func

theorem familySetoid_equiv_iff {x : ZFSet} {a b : x.out.Type} :
  a ≈ b ↔ x.out.Func a ≈ x.out.Func b := by rfl

def family (x : ZFSet) := Quotient x.familySetoid

theorem familyOfMem {x y : ZFSet} (h : y ∈ x) : ∃ a, y.out.Equiv (x.out.Func a) := by
  rw [←PSet.mem_iff, ←mk_mem_iff, mk_out, mk_out]; exact h

noncomputable def familyEquiv (x : ZFSet) : x.family ≃ x.toSet where
  toFun a := ⟨⟦x.out.Func a.out⟧, by
    simp; conv => rhs; rw [←x.out_eq]
    simp only [mk_eq, mk_mem_iff]
    apply PSet.Mem.mk⟩
  invFun
  | ⟨y, h⟩ => ⟦Classical.choose (familyOfMem h)⟧
  left_inv := by
    intro a; simp
    have h : x.out.Func a.out ∈ x.out := PSet.Mem.mk _ _
    rw [←mk_mem_iff, mk_out] at h
    apply familyOfMem at h
    have := Classical.choose_spec h
    have := (Quotient.mk_out ((Quotient.out x).Func (Quotient.out a))).symm.trans this
    rw [Quotient.mk_eq_iff_out]
    exact this.symm
  right_inv
  | ⟨y, h⟩ => by
    simp at h
    apply familyOfMem at h
    have := Classical.choose_spec h
    simp; rw [←mk_eq, Quotient.mk_eq_iff_out]
    refine (this.trans ?_).symm
    exact (Quotient.mk_out (Classical.choose h)).symm

noncomputable def familyOfBFamily {α : Sort v} (x : ZFSet.{u}) (f : ∀ y ∈ x, α) : x.family → α :=
  λ a => f (x.familyEquiv a) (x.familyEquiv a).property

noncomputable def bfamilyOfFamily {α : Sort v} (x : ZFSet.{u}) (f : x.family → α) : ∀ y ∈ x, α :=
  λ y h => f (x.familyEquiv.invFun ⟨y, h⟩)

open Cardinal
def card (x : ZFSet.{u}) : Cardinal.{u} := #x.family

theorem card_eq {x : ZFSet.{u}} : lift.{u+1, u} (card x) = #(↥x.toSet) := by
  rw [←lift_id #(↥x.toSet)]
  simp only [card]
  rw [Cardinal.lift_mk_eq.{u,u+1,u+1}]
  exact ⟨x.familyEquiv⟩

theorem card_mono : x ⊆ y → card x ≤ card y := by
  intro h
  rw [←lift_le, card_eq, card_eq, Cardinal.le_def]
  refine ⟨⟨λ ⟨z, h₁⟩ => ⟨z, h h₁⟩, ?_⟩⟩
  intro ⟨z₁, h₁⟩ ⟨z₂, h₂⟩; simp

theorem card_empty : card ∅ = 0 := by
  rw [←lift_inj, card_eq, lift_zero, Cardinal.mk_eq_zero_iff]; simp

theorem card_powerset : card (powerset x) = 2 ^ card x := by
  rw [←lift_inj, card_eq, lift_power, lift_two, card_eq, ←mk_powerset, Cardinal.eq]
  refine ⟨⟨
    λ ⟨y, h⟩ => ⟨{ z | z ∈ y }, λ z h' => by simp at *; exact h h'⟩,
    λ ⟨s, _⟩ => ⟨x.sep s, by simp; intro; aesop⟩,
    ?_, ?_⟩⟩
  · intro ⟨y, h⟩; ext z; aesop
  · intro ⟨s, h⟩; ext z; aesop

theorem card_sUnion_range_le : card (sUnion (range f)) ≤ sum λ i => (f i).card := by
  rw [←lift_le, card_eq, lift_sum]
  simp_rw [card_eq]
  rw [←Cardinal.mk_sigma, Cardinal.le_def]
  simp [toSet]
  refine ⟨⟨
    λ ⟨y, h⟩ =>
      let ⟨i, h'⟩ := Classical.indefiniteDescription (λ i => y ∈ f i) h
      ⟨i, ⟨y, h'⟩⟩,
    ?_⟩⟩
  intro ⟨y, h₁⟩ ⟨z, h₂⟩ h
  simp at h; rcases h with ⟨h', h⟩
  rw [Subtype.heq_iff_coe_eq] at h
  · simp at h; simp [h]
  · intro z; simp [h']

end

noncomputable def replace (x : ZFSet) (f : ∀ y ∈ x, ZFSet) :=
  @range x.family (x.familyOfBFamily f)

theorem mem_replace : y ∈ replace x f ↔ ∃ z h, y = f z h := by
  simp [replace]; constructor
  · intro ⟨a, h₁⟩; subst h₁
    exists x.familyEquiv a, (x.familyEquiv a).property
  · intro ⟨y, h₁, h₂⟩; subst h₂
    exists x.familyEquiv.invFun ⟨y, h₁⟩
    simp [familyOfBFamily]

noncomputable def rank (x : ZFSet.{u}) : Ordinal.{u} :=
  Quotient.liftOn x PSet.rank PSet.rank_eq_of_equiv

variable {x y : ZFSet}

theorem rank_lt_of_mem : y ∈ x → y.rank < x.rank := by
  induction' x using Quotient.inductionOn with x
  induction' y using Quotient.inductionOn with y
  apply PSet.rank_lt_of_mem

theorem rank_le_of_mem_rank_lt : (∀ y ∈ x, y.rank < α) → x.rank ≤ α := by
  intro h
  induction' x using Quotient.inductionOn with x
  apply PSet.rank_le_of_mem_rank_lt
  intro y h'
  apply h ⟦y⟧
  simp; exact h'

theorem rank_mono : x ⊆ y → x.rank ≤ y.rank := by
  intro h
  apply rank_le_of_mem_rank_lt
  intro z h₁; apply rank_lt_of_mem; exact h h₁

theorem rank_empty : (∅ : ZFSet).rank = 0 := by
  rw [←Ordinal.le_zero]; apply rank_le_of_mem_rank_lt; simp

theorem rank_singleton : ({x} : ZFSet).rank = x.rank + 1 := by
  apply le_antisymm
  · apply rank_le_of_mem_rank_lt; simp
  · simp; apply rank_lt_of_mem; simp

theorem rank_pair : ({x, y} : ZFSet).rank = max x.rank y.rank + 1 := by
  apply le_antisymm
  · apply rank_le_of_mem_rank_lt; simp
  · simp; constructor <;> apply rank_lt_of_mem <;> simp

theorem rank_union : (x ∪ y).rank = max x.rank y.rank := by
  apply le_antisymm
  · apply rank_le_of_mem_rank_lt
    intro z h; simp at h; rcases h with h | h
    · apply lt_max_of_lt_left; exact rank_lt_of_mem h
    · apply lt_max_of_lt_right; exact rank_lt_of_mem h
  · simp; constructor <;> apply rank_mono <;> intro <;> aesop

theorem rank_insert : (insert x y).rank = max (x.rank + 1) y.rank := by
  have : insert x y = {x} ∪ y := by ext; simp
  rw [this, rank_union, rank_singleton]

theorem rank_ofNat : (ofNat n).rank = n := by
  induction n with
  | zero => simp [rank_empty]
  | succ n ih => simp [rank_insert, ih, Order.le_succ]

theorem rank_omega : omega.rank = Ordinal.omega := by
  apply le_antisymm
  · apply rank_le_of_mem_rank_lt
    intro y h; simp [mem_omega_iff] at h
    rcases h with ⟨n, h⟩; subst h
    simp [rank_ofNat, Ordinal.lt_omega]
  · simp [Ordinal.omega_le]
    intro n; rw [←rank_ofNat]
    apply le_of_lt; apply rank_lt_of_mem
    simp [mem_omega_iff]

theorem rank_powerset : (powerset x).rank = x.rank + 1 := by
  apply le_antisymm
  · apply rank_le_of_mem_rank_lt
    intro y h; simp at h; simp [Order.lt_succ_iff]; exact rank_mono h
  · rw [←rank_singleton]; apply rank_mono
    intro y h; simp at h; simp [h, subset_refl]

theorem rank_sUnion_le : (⋃₀ x : ZFSet).rank ≤ x.rank := by
  apply rank_le_of_mem_rank_lt
  intro y h; simp at h; rcases h with ⟨z, h₂, h₃⟩
  trans <;> apply rank_lt_of_mem <;> assumption

theorem rank_range {f : α → ZFSet} : (range f).rank = Ordinal.sup λ i => rank (f i) + 1 := by
  apply le_antisymm
  · apply rank_le_of_mem_rank_lt
    simp; intro i
    rw [←Order.succ_le_iff]
    apply Ordinal.le_sup
  · apply Ordinal.sup_le
    intro i; simp; apply rank_lt_of_mem; simp



noncomputable def V (α : Ordinal.{u}) : ZFSet.{u} :=
  α.limitRecOn ∅ (λ _ ih => powerset ih)
    (λ α _ ih => sUnion (range (Ordinal.familyOfBFamily α λ β h => ih β h)))

theorem V_zero : V 0 = ∅ := by simp [V]

theorem V_succ : V (Order.succ α) = powerset (V α) := by simp [V]

theorem V_limit {α : Ordinal.{u}} (h : α.IsLimit) : V α = sUnion (range (Ordinal.familyOfBFamily α λ β _ => V β)) := by
  simp [V, Ordinal.limitRecOn_limit (h := h)]

theorem mem_V_limit {α : Ordinal.{u}} (h : α.IsLimit) : x ∈ V α ↔ ∃ β < α, x ∈ V β := by
  simp [V_limit h, Ordinal.mem_brange]

lemma V_transitive : (V α).IsTransitive := by
  induction' α using Ordinal.induction with α ih
  rcases α.zero_or_succ_or_limit with h | ⟨α, h⟩ | h
  · simp [h, V_zero]
  · subst h
    simp [V_succ]
    apply IsTransitive.powerset
    apply ih
    simp
  · simp [V_limit h]
    apply IsTransitive.sUnion'
    intro x h₁; simp [Ordinal.mem_brange] at h₁
    rcases h₁ with ⟨β, h₁, h₂⟩; subst h₂
    exact ih _ h₁

theorem V_strict_mono : α < β → V α ∈ V β := by
  intro h
  induction' β using Ordinal.induction with β ih
  rcases β.zero_or_succ_or_limit with h₁ | ⟨β, h₁⟩ | h₁
  · simp [h₁, Ordinal.not_lt_zero] at h
  · subst h₁; simp at h; simp [V_succ]
    rcases lt_or_eq_of_le h with h | h
    · apply V_transitive; exact ih β (Order.lt_succ β) h
    · simp [h, subset_refl]
  · simp [mem_V_limit h₁]
    exists Order.succ α; constructor
    · exact h₁.right _ h
    · simp [V_succ, subset_refl]

theorem V_mono : α ≤ β → V α ⊆ V β := by
  intro h
  rcases lt_or_eq_of_le h with h | h
  · apply V_transitive; exact V_strict_mono h
  · simp [h, subset_refl]

theorem mem_V_rank {x : ZFSet} : x ∈ V (x.rank + 1) := by
  induction' x using inductionOn with x ih
  simp [V_succ]
  intro _ h₂
  apply V_mono _ (ih _ h₂)
  simp; exact rank_lt_of_mem h₂

theorem mem_V_iff : x ∈ V α ↔ x.rank < α := by
  constructor
  · intro h
    induction' α using Ordinal.induction with α ih generalizing x
    rcases α.zero_or_succ_or_limit with h₁ | ⟨α, h₁⟩ | h₁
    · simp [h₁, V_zero] at h
    · simp [h₁, V_succ] at *
      apply rank_le_of_mem_rank_lt
      intro y h₂; apply ih
      · rfl
      · apply h; exact h₂
    · simp [mem_V_limit h₁] at h
      rcases h with ⟨β, h₂, h₃⟩
      apply ih _ h₂ at h₃
      exact h₃.trans h₂
  · intro h; apply V_mono _ mem_V_rank; simp [h]

theorem card_V_lt_of_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
  α < κ.ord → (V α).card < κ := by
  intro h
  induction' α using Ordinal.induction with α ih
  rcases α.zero_or_succ_or_limit with h₁ | ⟨α, h₁⟩ | h₁
  · simp [h₁, V_zero, card_empty]
    have := (Cardinal.ord_isLimit (le_of_lt hκ.1)).pos
    simp [Cardinal.lt_ord] at this
    exact this
  · subst h₁; simp [V_succ, card_powerset] at *
    apply hκ.2.2.2
    apply ih
    · rfl
    · trans Order.succ α
      · simp
      · exact h
  · simp [V_limit h₁]
    apply lt_of_le_of_lt (card_sUnion_range_le)
    apply Cardinal.sum_lt_of_isRegular hκ.2.1
    · simp [Cardinal.lt_ord] at h; simp [h]
    · intro i
      simp [Ordinal.familyOfBFamily, Ordinal.familyOfBFamily']
      apply ih
      · apply Ordinal.typein_lt_self
      · trans; apply Ordinal.typein_lt_self; exact h

theorem card_lt_of_mem_V_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
  x ∈ V κ.ord → x.card < κ := by
  intro h
  apply lt_of_le_of_lt (card_mono (V_transitive _ mem_V_rank))
  apply card_V_lt_of_inaccessible hκ
  apply (Cardinal.ord_isLimit (le_of_lt hκ.1)).succ_lt
  rw [←mem_V_iff]
  exact h

theorem replace_mem_V_of_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
  x ∈ V κ.ord → (∀ y h, f y h ∈ V κ.ord) → x.replace f ∈ V κ.ord := by
  intro h₁ h₂
  simp [mem_V_iff, replace, rank_range]
  apply Cardinal.sup_lt_ord_of_isRegular hκ.2.1
  · rw [←card]; exact card_lt_of_mem_V_inaccessible hκ h₁
  · intro i
    apply (Cardinal.ord_isLimit (le_of_lt hκ.1)).succ_lt
    simp [←mem_V_iff]
    apply h₂

end ZFSet
