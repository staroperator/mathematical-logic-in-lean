import Mathlib.Data.PFun
import Mathlib.Tactic.ApplyAt
import MathematicalLogic.Vec

namespace Part

theorem dom_of_mem {o : Part α} (h : a ∈ o) : o.Dom := dom_iff_mem.mpr ⟨a, h⟩

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

@[simp] theorem bindVec_nil {v : Vec (Part α) 0} : bindVec v = Part.some []ᵥ := by
  ext; simp [Vec.eq_nil]

theorem bindVec_cons {v : Vec (Part α) (n + 1)} :
  bindVec v = v.head >>= λ a => bindVec v.tail >>= λ w => some (a ∷ᵥ w) := by
  ext u; rw [Vec.eq_cons u]; simp [Vec.head, Fin.forall_fin_succ]

@[simp] theorem bindVec_1 {v : Vec (Part α) 1} : bindVec v = v 0 >>= λ a => some [a]ᵥ := by
  simp [bindVec_cons, Vec.head]

@[simp] theorem bindVec_2 {v : Vec (Part α) 2} :
  bindVec v = v 0 >>= λ a => v 1 >>= λ b => some [a, b]ᵥ := by
  simp [bindVec_cons, Vec.head, bind_assoc]

@[simp] theorem bindVec_3 {v : Vec (Part α) 3} :
  bindVec v = v 0 >>= λ a => v 1 >>= λ b => v 2 >>= λ c => some [a, b, c]ᵥ := by
  simp [bindVec_cons, Vec.head, bind_assoc]

def natrec (a : Part α) (f : ℕ → α →. α) (n : ℕ) : Part α :=
  Nat.rec a (λ n ih => ih >>= λ a => f n a) n

theorem natrec_zero : natrec a f 0 = a := rfl

theorem natrec_succ : natrec a f (n + 1) = natrec a f n >>= λ a => f n a := rfl

theorem natrec_dom_le : (natrec a f n).Dom → k ≤ n → (natrec a f k).Dom := by
  intro h₁ h₂
  induction h₂ with
  | refl => exact h₁
  | step _ ih =>
    simp [natrec_succ] at h₁
    exact ih h₁.fst

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

variable [Zero α]
@[simp] theorem zero_lt_some_iff : 0 < some a ↔ 0 < a := by simp [zero_def]
theorem pos_iff : 0 < x ↔ ∃ a ∈ x, 0 < a := by simp [zero_def, some_lt_iff]
theorem pos_iff_get (h : x.Dom) : 0 < x ↔ 0 < x.get h := by
  simp [pos_iff]
  constructor
  · intro ⟨a, h₁, h₂⟩; rw [Part.get_eq_of_mem h₁]; exact h₂
  · intro h₁; exists x.get h, Part.get_mem h
theorem dom_of_pos (h : 0 < x) : x.Dom := by
  simp [pos_iff] at h; rcases h with ⟨_, h, _⟩; exact dom_of_mem h
@[simp] theorem bind_pos_iff {a : Part β} {f : β → Part α} : 0 < a.bind f ↔ ∃ x ∈ a, 0 < f x := by
  simp [pos_iff]; aesop

end

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
