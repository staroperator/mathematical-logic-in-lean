import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.VonNeumann

universe u v

theorem Cardinal.IsRegular.lift {c : Cardinal.{u}} (hc : c.IsRegular) : (lift.{v, u} c).IsRegular :=
  ⟨by simpa using hc.1, by simpa [← lift_ord, ← Ordinal.lift_cof] using hc.2⟩

open Cardinal in
theorem Cardinal.sum_lt_lift_of_isRegular' {ι : Type u} {f : ι → Cardinal.{v}}
    {c : Cardinal.{max u v}} (hc : IsRegular c) (hι : lift #ι < c) (hf : ∀ i, lift (f i) < c) :
    sum f < c := by
  refine (sum_lt_lift_of_isRegular hc hι hf).trans_le' ?_
  rw [←lift_sum, lift_id']

theorem ZFSet.rank_mk : rank (mk x) = PSet.rank x := rfl

namespace PSet

local instance typeSetoid (x : PSet) : Setoid x.Type where
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
  rw [←lift_le, card_eq, card_eq, Cardinal.le_def]
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

theorem lift_card_sUnion_range_le {α : Type u} [Small.{v, u} α] {f : α → ZFSet.{v}} :
  lift (card (sUnion (range f))) ≤ sum λ i => (f i).card := by
  -- rw [←lift_le.{max (u + 1) v}, lift_lift, ←lift_lift, card_eq, lift_sum]
  rw [←lift_le.{max u (v + 1)}, lift_lift, ←lift_lift.{v + 1}, card_eq, lift_sum]
  conv => rhs; arg 1; intro i; rw [←lift_lift.{v + 1}, card_eq]
  rw [←lift_sum, ←mk_sigma, ←mk_uLift, ←mk_uLift, Cardinal.le_def]
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

theorem card_V_lt_of_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
  α < κ.ord → (V_ α).card < κ := by
  intro h
  induction' α using Ordinal.induction with α ih
  rcases α.zero_or_succ_or_isSuccLimit with h₁ | ⟨α, h₁⟩ | h₁
  · simp [h₁, vonNeumann_zero, card_empty]
    have := (isSuccLimit_ord (le_of_lt hκ.1)).1
    simpa [← pos_iff_ne_zero] using this
  · subst h₁; simp [vonNeumann_succ, card_powerset] at *
    apply hκ.2.2
    apply ih
    · rfl
    · trans Order.succ α
      · simp
      · exact h
  · rw [vonNeumann_of_isSuccPrelimit h₁.isSuccPrelimit]
    refine lift_lt.1 (lift_card_sUnion_range_le.trans_lt ?_)
    apply sum_lt_lift_of_isRegular' hκ.isRegular.lift
    · rwa [Ordinal.mk_Iio_ordinal, lift_lift, lift_lt, ← lt_ord]
    · intro ⟨i, hi⟩
      simp at hi
      rw [lift_lt]
      exact ih i hi (hi.trans h)

theorem card_lt_of_mem_V_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
  x ∈ V_ κ.ord → x.card < κ := by
  intro h
  apply lt_of_le_of_lt (card_mono (isTransitive_vonNeumann _ _ (mem_vonNeumann_succ _)))
  apply card_V_lt_of_inaccessible hκ
  apply (isSuccLimit_ord (le_of_lt hκ.1)).succ_lt
  rwa [←mem_vonNeumann]

theorem image_mem_V_of_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) [Definable₁ f] :
  x ∈ V_ κ.ord → (∀ y ∈ x, f y ∈ V_ κ.ord) → image f x ∈ V_ κ.ord := by
  intro h₁ h₂
  rw [mem_vonNeumann, rank_image]
  apply lsub_lt_ord_of_isRegular hκ.isRegular
  · rw [←PSet.card]
    rw [←mk_out x] at h₁
    exact card_lt_of_mem_V_inaccessible hκ h₁
  · intro a
    rw [←mem_vonNeumann]
    apply h₂
    have := PSet.func'_mem_mk a
    rw [mk_out x] at this
    exact this

end ZFSet
