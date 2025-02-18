import Mathlib.Data.PFun
import Mathlib.Tactic.ApplyAt
import MathematicalLogic.Vec

namespace Part

def bindVec (v : Vec (Part α) n) : Part (Vec α n) :=
  ⟨∀ i, (v i).Dom, λ h i => (v i).get (h i)⟩

@[simp] theorem bindVec_dom : (bindVec v).Dom ↔ ∀ i, (v i).Dom := by rfl

@[simp] theorem mem_bindVec_iff : v ∈ bindVec w ↔ ∀ i, v i ∈ w i := by
  simp [bindVec]
  constructor
  · intro ⟨h₁, h₂⟩ i; subst h₂; simp; apply get_mem
  · intro h₁; exists λ i => (h₁ i).1
    ext i; apply get_eq_of_mem; apply h₁

@[simp] theorem bindVec_get : (bindVec v).get h = λ i => (v i).get (h i) := rfl

theorem bindVec_some : bindVec (λ i => some (v i)) = some v := by
  simp [bindVec, eq_some_iff]
theorem bindVec_some_1 : bindVec [some a]ᵥ = some [a]ᵥ := by
  rw [←bindVec_some]; congr; ext i; cases i using Fin.cases1; simp

section

variable {α : Type u} [PartialOrder α]

instance (priority := high) : PartialOrder (Part α) where
  le x y := ∀ a ∈ x, ∃ b ∈ y, a ≤ b
  le_refl x a ha := ⟨a, ha, le_refl a⟩
  le_antisymm x y h₁ h₂ := by
    ext a
    constructor
    · intro ha
      rcases h₁ a ha with ⟨b, hb, h₃⟩
      rcases h₂ b hb with ⟨c, hc, h₄⟩
      have := Part.mem_unique ha hc; subst this
      rw [le_antisymm h₃ h₄]; exact hb
    · intro ha
      rcases h₂ a ha with ⟨b, hb, h₃⟩
      rcases h₁ b hb with ⟨c, hc, h₄⟩
      have := Part.mem_unique ha hc; subst this
      rw [le_antisymm h₃ h₄]; exact hb
  le_trans x y z h₁ h₂ a ha := by
    rcases h₁ a ha with ⟨b, hb, h₃⟩
    rcases h₂ b hb with ⟨c, hc, h₄⟩
    exact ⟨c, hc, le_trans h₃ h₄⟩
  lt x y := ∃ b ∈ y, ∀ a ∈ x, a < b
  lt_iff_le_not_le x y := by
    simp only [not_forall, Classical.not_imp, not_exists, not_and, exists_prop]
    constructor
    · intro ⟨b, hb, h⟩
      constructor
      · intro a ha
        exact ⟨b, hb, le_of_lt (h a ha)⟩
      · exact ⟨b, hb, λ a ha => not_le_of_lt (h a ha)⟩
    · intro ⟨h, ⟨b, hb, h'⟩⟩
      exists b, hb
      intro a ha
      apply lt_of_le_not_le
      · rcases h a ha with ⟨c, hc, h''⟩
        rw [←mem_unique hb hc] at h''
        exact h''
      · exact h' a ha

variable {x y : Part α} {a b : α}

theorem le_iff : x ≤ y ↔ ∀ a ∈ x, ∃ b ∈ y, a ≤ b := by rfl
theorem lt_iff : x < y ↔ ∃ b ∈ y, ∀ a ∈ x, a < b := by rfl
@[simp] theorem none_le : none ≤ x := by simp [le_iff]
@[simp] theorem none_lt_some : none < some a := by simp [lt_iff]
@[simp] theorem some_le_some_iff : some a ≤ some b ↔ a ≤ b := by simp [le_iff]
@[simp] theorem some_lt_some_iff : some a < some b ↔ a < b := by simp [lt_iff]
theorem some_le_iff : some a ≤ x ↔ ∃ b ∈ x, a ≤ b := by simp [le_iff]
theorem some_lt_iff : some a < x ↔ ∃ b ∈ x, a < b := by simp [lt_iff]

end

theorem zero_def [Zero α] : (0 : Part α) = some 0 := rfl

def find_aux (f : ℕ →. ℕ)
  (h : ∃ n, 0 < f n ∧ ∀ k < n, (f k).Dom)
  (n : ℕ) (ih : ∀ k < n, 0 ∈ f k) : {n : ℕ // 0 < f n ∧ ∀ k < n, 0 ∈ f k} :=
  have h₁ : n ≤ Classical.choose h := by
    rcases (Classical.choose_spec h).left with ⟨x, h₁, h₂⟩
    simp [zero_def] at h₂
    by_contra h₃
    simp at h₃
    apply ih at h₃
    rw [Part.mem_unique h₁ h₃] at h₂
    contradiction
  have h₂ : (f n).Dom := by
    apply Nat.eq_or_lt_of_le at h₁
    rcases h₁ with h₁ | h₁
    · rw [Part.dom_iff_mem, h₁]
      rcases (Classical.choose_spec h).left with ⟨x, h₂, _⟩
      exists x
    · apply (Classical.choose_spec h).right
      exact h₁
  match h₃ : (f n).get h₂ with
  | 0 =>
    have h₄ : n < Classical.choose h := by
      by_contra h₄
      apply eq_of_ge_of_not_gt h₁ at h₄
      rcases (Classical.choose_spec h).left with ⟨y, h₅, h₆⟩
      simp [zero_def] at h₆
      rw [h₄] at h₅
      apply Part.mem_unique (Part.get_mem h₂) at h₅
      simp [h₅] at h₃
      simp [h₃] at h₆
    find_aux f h (n + 1) (by
      intros k h₅
      rw [Nat.add_one, Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at h₅
      rcases h₅ with h₅ | h₅
      · apply ih; exact h₅
      · rw [h₅, ←h₃]
        apply Part.get_mem)
  | x + 1 => ⟨n, ⟨x + 1, by rw [Nat.add_one, ←h₃]; apply Part.get_mem, by simp [zero_def]⟩, ih⟩
termination_by Classical.choose h - n

def find (f : ℕ →. ℕ) : Part ℕ := ⟨_, λ h => find_aux f h 0 (by simp)⟩

theorem mem_find_iff : n ∈ find f ↔ 0 < f n ∧ ∀ k < n, 0 ∈ f k := by
  constructor
  · intro ⟨h₁, h₂⟩
    simp_rw [←h₂]
    exact (find_aux f _ 0 _).property
  · intro ⟨⟨x, h₁, h₂⟩, h₃⟩
    simp [zero_def] at h₂
    have h₄ : (find f).Dom := by
      simp [find]
      exists n
      constructor
      · exists x, h₁; simp [zero_def, h₂]
      · intro k h₄
        rcases h₃ k h₄ with ⟨h₅, _⟩
        exact h₅
    let m := (find f).get h₄
    rcases lt_trichotomy m n with h₅ | h₅ | h₅
    · apply h₃ at h₅
      rcases (find_aux f _ 0 _).property.left with ⟨x, h₆, h₇⟩
      apply Part.mem_unique h₆ at h₅
      simp [h₅, zero_def] at h₇
    · simp_rw [←h₅]; apply Part.get_mem
    · apply (find_aux f _ 0 _).property.right at h₅
      apply Part.mem_unique h₁ at h₅
      simp [h₅] at h₂

theorem find_dom : (find f).Dom ↔ ∃ n, 0 < f n ∧ ∀ k < n, (f k).Dom := by rfl

end Part
