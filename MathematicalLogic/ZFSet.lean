import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.ZFC.Rank

universe u v

theorem ZFSet.rank_mk : rank (mk x) = PSet.rank x := rfl

namespace PSet

private instance typeSetoid (x : PSet) : Setoid x.Type where
  r a b := x.Func a ≈ x.Func b
  iseqv.refl _ := Equiv.refl _
  iseqv.symm := Equiv.symm
  iseqv.trans := Equiv.trans

def Type' (x : PSet) := Quotient (typeSetoid x)

def Func' (x : PSet) (a : x.Type') : ZFSet :=
  Quotient.liftOn a (ZFSet.mk ∘ x.Func) λ _ _ h => Quotient.sound h

variable {x : PSet}

theorem func'_inj : Function.Injective x.Func' :=
  λ a₁ a₂ => Quotient.inductionOn₂ a₁ a₂ λ _ _ h => Quotient.sound (Quotient.exact (s := setoid) h)

theorem func'_mem_mk (a) : x.Func' a ∈ ZFSet.mk x :=
  Quotient.inductionOn a λ _ => ZFSet.mk_mem_iff.2 (func_mem _ _)

theorem mem_mk_of_func' {x : PSet} : ∀ y ∈ ZFSet.mk x, ∃ a, y = x.Func' a :=
  λ y => Quotient.inductionOn y λ _ ⟨a, h⟩ => ⟨⟦a⟧, Quotient.sound h⟩

open Cardinal

def card (x : PSet.{u}) : Cardinal.{u} := #x.Type'

theorem card_eq : lift.{u+1, u} (card x) = #(ZFSet.mk x).toSet := by
  rw [←lift_id #(ZFSet.mk x).toSet, card, lift_mk_eq.{u,u+1,u+1}]
  refine ⟨_root_.Equiv.ofBijective (λ a => ⟨x.Func' a, func'_mem_mk a⟩) ⟨?_, ?_⟩⟩
  · intro _ _ h; simp at h; exact func'_inj h
  · intro ⟨_, h⟩; simp; exact (mem_mk_of_func' _ h).imp λ _ => Eq.symm

theorem card_congr {x y : PSet.{u}} : Equiv x y → card x = card y := by
  intro h
  apply ZFSet.sound at h
  rw [←lift_inj, card_eq, card_eq, h]

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

@[simp] theorem sep_subset : ZFSet.sep p x ⊆ x := by
  intro; simp; intro h _; exact h

open Cardinal

def card : ZFSet.{u} → Cardinal.{u} := Quotient.lift PSet.card λ _ _ => PSet.card_congr

theorem card_eq {x : ZFSet.{u}} : lift.{u+1, u} (card x) = #x.toSet :=
  Quotient.inductionOn x λ _ => PSet.card_eq

theorem card_mono : x ⊆ y → card x ≤ card y := by
  intro h
  rw [←lift_le, card_eq, card_eq, le_def]
  refine ⟨⟨λ ⟨z, h₁⟩ => ⟨z, h h₁⟩, ?_⟩⟩
  intro ⟨z₁, h₁⟩ ⟨z₂, h₂⟩; simp

theorem card_empty : card ∅ = 0 := by
  rw [←lift_inj, card_eq, lift_zero, mk_eq_zero_iff]; simp

theorem card_powerset : card (powerset x) = 2 ^ card x := by
  rw [←lift_inj, card_eq, lift_power, lift_two, card_eq, ←mk_powerset, Cardinal.eq]
  refine ⟨⟨
    λ ⟨y, h⟩ => ⟨{ z | z ∈ y }, λ _ h' => by simp at *; exact h h'⟩,
    λ ⟨s, _⟩ => ⟨x.sep (· ∈ s), by simp⟩,
    ?_, ?_⟩⟩
  · intro ⟨y, h⟩; simp at h; ext; simp; apply h
  · intro ⟨s, h⟩; ext; simp; apply h

theorem card_sUnion_range_le [Small.{u} α] {f : α → ZFSet.{u}} :
  card (sUnion (range f)) ≤ sum λ i => (f i).card := by
  rw [←lift_le, card_eq, lift_sum]
  simp_rw [card_eq]
  rw [←mk_sigma, le_def]
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

theorem rank_ofNat : rank (ofNat n) = n := by
  induction n with
  | zero => simp [rank_empty]
  | succ n ih => simp [rank_insert, ih, Order.le_succ]

theorem rank_omega : rank omega = Ordinal.omega0 := by
  apply le_antisymm
  · rw [rank_le_iff]
    intro y h; simp [mem_omega_iff] at h
    rcases h with ⟨n, h⟩; subst h
    simp [rank_ofNat, Ordinal.lt_omega0]
  · simp [Ordinal.omega0_le]
    intro n; rw [←rank_ofNat]
    apply le_of_lt; apply rank_lt_of_mem
    simp [mem_omega_iff]

theorem rank_image {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f] :
  rank (image f x) = Ordinal.lsub λ a => rank (f (x.out.Func' a)) := by
  apply le_antisymm
  · simp [rank_le_iff]
    intro y h
    rw [←mk_out x] at h
    apply PSet.mem_mk_of_func' at h
    rcases h with ⟨a, h⟩
    rw [h]
    apply Ordinal.lt_lsub
  · apply Ordinal.lsub_le
    intro a
    apply rank_lt_of_mem
    have := @PSet.func'_mem_mk x.out a
    rw [mk_out] at this
    simp; exact ⟨_, this, rfl⟩

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
    · exact h₁.succ_lt h
    · simp [V_succ, subset_refl]

theorem V_mono : α ≤ β → V α ⊆ V β := by
  intro h
  rcases lt_or_eq_of_le h with h | h
  · apply V_transitive; exact V_strict_mono h
  · simp [h]

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
      rw [rank_le_iff]
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
    have := (isLimit_ord (le_of_lt hκ.1)).pos
    simp [lt_ord] at this
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
    apply sum_lt_of_isRegular hκ.2.1
    · simp [lt_ord] at h; simp [h]
    · intro i
      apply ih
      · apply Ordinal.typein_lt_self
      · trans; apply Ordinal.typein_lt_self; exact h

theorem card_lt_of_mem_V_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
  x ∈ V κ.ord → x.card < κ := by
  intro h
  apply lt_of_le_of_lt (card_mono (V_transitive _ mem_V_rank))
  apply card_V_lt_of_inaccessible hκ
  apply (isLimit_ord (le_of_lt hκ.1)).succ_lt
  rw [←mem_V_iff]
  exact h

theorem image_mem_V_of_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) [Definable₁ f] :
  x ∈ V κ.ord → (∀ y ∈ x, f y ∈ V κ.ord) → image f x ∈ V κ.ord := by
  intro h₁ h₂
  rw [mem_V_iff, rank_image]
  apply lsub_lt_ord_of_isRegular hκ.2.1
  · rw [←PSet.card]
    rw [←mk_out x] at h₁
    exact card_lt_of_mem_V_inaccessible hκ h₁
  · intro a
    rw [←mem_V_iff]
    apply h₂
    have := PSet.func'_mem_mk a
    rw [mk_out x] at this
    exact this

end ZFSet
