import MathematicalLogic.Part
import MathematicalLogic.Computability.Primrec

inductive Partrec : ℕ → Type where
| const : ℕ → Partrec n
| succ : Partrec 1
| proj : Fin n → Partrec n
| comp : Partrec n → (Fin n → Partrec m) → Partrec m
| prec : Partrec n → Partrec (n + 2) → Partrec (n + 1)
| mu : Partrec (n + 1) → Partrec n

namespace Partrec

abbrev comp₁ (f : Partrec 1) (g : Partrec n) := f.comp [g]ᵥ
abbrev comp₂ (f : Partrec 2) (g₁ g₂ : Partrec n) := f.comp [g₁, g₂]ᵥ
abbrev comp₃ (f : Partrec 3) (g₁ g₂ g₃ : Partrec n) := f.comp [g₁, g₂, g₃]ᵥ

def eval : Partrec n → Vec ℕ n →. ℕ
| const n, _ => Part.some n
| succ, v => Part.some v.head.succ
| proj i, v => Part.some (v i)
| comp f g, v => Part.bindVec (λ i => (g i).eval v) >>= f.eval
| prec f g, v => Part.natrec (f.eval v.tail) (λ n ih => ih >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v.tail)) v.head
| mu f, v => Part.find λ n => f.eval (n ∷ᵥ v)

instance : CoeFun (Partrec n) (λ _ => Vec ℕ n →. ℕ) := ⟨eval⟩
@[simp] theorem zero_eval : const n v = Part.some n := rfl
@[simp] theorem succ_eval : succ v = Part.some v.head.succ := rfl
@[simp] theorem proj_eval : proj i v = Part.some (v i) := rfl
@[simp] theorem comp_eval : comp f g v = Part.bindVec (λ i => g i v) >>= f := rfl
theorem prec_eval : (prec f g) v = Part.natrec (f.eval v.tail) (λ n ih => ih >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v.tail)) v.head := rfl
theorem prec_eval_zero : (prec f g) (0 ∷ᵥ v) = f.eval v := Part.natrec_zero
theorem prec_eval_succ : (prec f g) (n.succ ∷ᵥ v) = eval (prec f g) (n ∷ᵥ v) >>= λ m => g.eval (n ∷ᵥ m ∷ᵥ v) := by
  simp [prec_eval, Part.natrec_succ]
@[simp] theorem mu_eval : mu f v = Part.find λ n => f.eval (n ∷ᵥ v) := rfl

def Total (f : Partrec n) := ∀ v, (f v).Dom

def ofPrim : Primrec n → Partrec n
| .const n => const n
| .succ => succ
| .proj i => proj i
| .comp f g => comp (ofPrim f) (λ i => ofPrim (g i))
| .prec f g => prec (ofPrim f) (ofPrim g)
@[simp] theorem ofPrim_eval : (ofPrim f) v = Part.some (f v) := by
  induction f with simp [ofPrim]
  | comp f g ih₁ ih₂ =>
    simp [Part.eq_some_iff]
    exists λ i => g i v
    simp [ih₁, ih₂]
  | prec f g ih₁ ih₂ =>
    simp [Primrec.prec_eval, prec_eval, Vec.head, ih₁]
    generalize v 0 = n, v.tail = v
    induction n with simp [Part.natrec_zero, Part.natrec_succ]
    | succ n ih => simp [ih]; simp [ih₂]
theorem ofPrim_total : Total (ofPrim f) := by
  intro; simp

abbrev _root_.Primrec.toPart : Primrec n → Partrec n := Partrec.ofPrim

def loop : Partrec n := mu (ofPrim (.const 0))
@[simp] theorem loop_eval : loop v = Part.none := by
  simp [loop, Part.eq_none_iff]
  intro n h
  simp [Part.mem_find_iff, Part.zero_def] at h

def cov (f : Partrec (n + 2)) : Partrec (n + 1) :=
  (const 0).prec ((ofPrim .rcons).comp₃ (proj 0) (proj 1) f)
theorem cov_dom {f : Partrec (n + 2)} (hf : ∀ a b, (f (a ∷ᵥ b ∷ᵥ v)).Dom) :
  ∀ m, (f.cov (m ∷ᵥ v)).Dom := by
  intro m
  induction m with
  | zero => simp [cov, prec_eval_zero]
  | succ m ih =>
    rw [cov, prec_eval_succ, ←cov]
    simp; exists ih; apply hf
theorem cov_eval {f : Partrec (n + 2)} (hf : ∀ a b, (f (a ∷ᵥ b ∷ᵥ v)).Dom) :
  f.cov (m ∷ᵥ v) = Part.some (Vec.paired λ i : Fin m =>
    (f (i ∷ᵥ (f.cov (i ∷ᵥ v)).get (cov_dom hf _) ∷ᵥ v)).get (hf _ _)) := by
  induction m with
  | zero => simp [cov, prec_eval_zero, Vec.paired]
  | succ m ih =>
    nth_rw 1 [cov]; rw [prec_eval_succ, ←cov]
    simp [ih, Part.eq_some_iff]
    refine ⟨_, _, Part.get _ (hf _ _), ⟨Part.get_mem (hf _ _), rfl, rfl⟩, ?_⟩
    simp [Primrec.rcons_eval]
    congr! with i
    cases i using Fin.lastCases <;> simp [ih]

/-- Course-of-values recursion. For simplicity we assume the totality of `f` on the first two arguments. -/
def covrec (f : Partrec (n + 2)) : Partrec (n + 1) :=
  (ofPrim .vget).comp₂ (f.cov.comp (succ.comp₁ (proj 0) ∷ᵥ (proj ·.succ))) (proj 0)
theorem covrec_dom {f : Partrec (n + 2)} (hf : ∀ a b, (f (a ∷ᵥ b ∷ᵥ v)).Dom) :
  ∀ m, (f.covrec (m ∷ᵥ v)).Dom := by
  intro m; simp [covrec, Fin.forall_fin_succ]; apply cov_dom hf
theorem covrec_eval {f : Partrec (n + 2)} (hf : ∀ a b, (f (a ∷ᵥ b ∷ᵥ v)).Dom) :
  f.covrec (m ∷ᵥ v) = f (m ∷ᵥ Vec.paired (λ i : Fin m => (f.covrec (i ∷ᵥ v)).get (covrec_dom hf _)) ∷ᵥ v) := by
  simp [covrec, Part.bindVec_some, Part.bindVec_cons, Vec.head, Vec.tail, Function.comp_def]
  rw [cov_eval hf]; simp [Primrec.vget_eval' (Nat.lt_succ_self m)]
  congr!; simp [Part.get_eq_iff_mem]; rw [cov_eval hf]; simp
  congr! with i; rw [cov_eval hf]; simp [Primrec.vget_eval']

/--
  `bd f (k ∷ᵥ v)` replaces all unbounded `mu` in `f v` with a `Primrec.bdMu` bounded by `k`;
  it returns `0` for `Part.none`, and `x + 1` for `Part.some x`.
  
  `bd` is similar to `Nat.Partrec.Code.evaln` in mathlib, although `bd` itself is not primitive recursive
  (since `bd f` is equivalent to `f + 1` when `f` is primitive recursive).
  -/
def bd : Partrec n → Primrec (n + 1)
| const n => .const (n + 1)
| succ => Primrec.succ.comp₁ (Primrec.succ.comp₁ (.proj 1))
| proj i => Primrec.succ.comp₁ (.proj i.succ)
| comp f g =>
  .ite (.andv λ i => (g i).bd)
    (f.bd.comp (.proj 0 ∷ᵥ λ i => Primrec.pred.comp₁ (g i).bd))
    .zero
| prec f g =>
  (Primrec.prec f.bd
    (.ite (.proj 1)
      (g.bd.comp (.proj 2 ∷ᵥ .proj 0 ∷ᵥ Primrec.pred.comp₁ (.proj 1) ∷ᵥ λ i => .proj i.succ.succ.succ))
      .zero)).swap
| mu f =>
  let k := (Primrec.bdMu (Primrec.pred.comp₁ f.bd.swap)).comp (.proj 0 ∷ᵥ .proj)
  .ite (.lt k (.proj 0))
    (.ite (.bdForall k (f.bd.swap)) (Primrec.succ.comp₁ k) .zero)
    .zero

theorem bd_mono : bd f (k ∷ᵥ v) = m + 1 → k' ≥ k → bd f (k' ∷ᵥ v) = m + 1 := by
  intro h hk
  induction f generalizing m k k' with simp [bd] at h ⊢
  | const | succ | proj => simp [h]
  | comp f g ih₁ ih₂ =>
    split at h
    next h₁ =>
      simp_vec at h ⊢
      simp [λ i => ih₂ i (Nat.sub_add_cancel (h₁ i)).symm hk]; exact ih₁ h hk
    next => simp at h
  | prec f g ih₁ ih₂ =>
    simp [Primrec.prec_eval] at h ⊢
    generalize v 0 = a, v.tail = v at h ⊢
    induction a generalizing m v with
    | zero =>
      simp at h ⊢; exact ih₁ h hk
    | succ a ih =>
      simp at h ⊢; simp_vec at h ⊢
      split at h
      next h₂ =>
        simp [ih _ (Nat.sub_add_cancel h₂).symm]
        exact ih₂ h hk
      next => simp at h
  | mu f ih =>
    generalize hk₁ : Primrec.bdMu _ _ = k₁ at h
    generalize hk₂ : Primrec.bdMu _ _ = k₂
    simp_vec at hk₁ hk₂
    split at h <;> try simp at h
    next h₁ =>
      split at h <;> try simp at h
      subst h
      next h₂ =>
        have : k₂ = k₁ := by
          subst hk₂
          apply Primrec.bdMu_eval_eq
          · exact h₁.le.trans hk
          · intro k'' hk'
            specialize h₂ k'' hk'
            have h₃ := hk'; rw [←hk₁] at h₃
            apply Primrec.bdMu_eval_gt at h₃
            simp [Nat.sub_eq_zero_iff_le] at h₃
            apply h₃.antisymm at h₂
            simp [ih h₂ hk]
          · rw [←hk₁] at h₁
            apply Primrec.bdMu_eval_lt_self at h₁
            simp [hk₁] at h₁
            simp [ih (Nat.sub_add_cancel h₁).symm hk]
        subst this
        simp [h₁.trans_le hk]
        intro k₃ h₃ h₄
        specialize h₂ k₃ h₃
        have := ih (Nat.sub_add_cancel h₂).symm hk; simp [this] at h₄

theorem bd_sound : bd f (k ∷ᵥ v) = m + 1 → m ∈ f v := by
  intro h
  induction f generalizing m k with (simp [bd] at h; try simp)
  | const | succ | proj => simp [Vec.head, h]
  | comp f g ih₁ ih₂ =>
    split at h <;> try simp at h
    next h₁ =>
      exists λ i => (g i).bd (k ∷ᵥ v) - 1
      constructor
      · intro i; apply ih₂ (k := k); simp [Nat.sub_add_cancel (h₁ i)]
      · simp_vec at h; exact ih₁ h
  | prec f g ih₁ ih₂ =>
    rw [Vec.eq_cons v]; simp [Vec.head]
    generalize v 0 = a, v.tail = v at h ⊢
    induction a generalizing m with
    | zero => simp [Primrec.prec_eval_zero] at h; simp [prec_eval_zero]; exact ih₁ h
    | succ a ih =>
      simp [Primrec.prec_eval_succ] at h
      split at h <;> try simp at h
      next h₁ =>
        simp_vec at h
        simp [prec_eval_succ]
        refine ⟨_, ?_, ih₂ h⟩
        apply ih
        simp [Nat.sub_add_cancel h₁]
  | mu f ih =>
    generalize h₁ : Primrec.bdMu _ _ = k' at h
    simp_vec at h₁
    split at h <;> try simp at h
    next h₂ =>
      split at h <;> try simp at h
      next h₃ =>
        subst h; simp [Part.mem_find_iff]
        constructor
        · simp [Part.pos_iff]
          have : 1 < f.bd (k ∷ᵥ k' ∷ᵥ v) := by
            have := h₂; rw [←h₁] at this
            apply Primrec.bdMu_eval_lt_self at this
            simp [h₁] at this; exact this
          exists f.bd (k ∷ᵥ k' ∷ᵥ v) - 1
          constructor
          · apply ih; rw [Nat.sub_add_cancel this.le]
          · simp [this]
        · intro k'' hk'
          specialize h₃ k'' hk'
          have h₄ := hk'; rw [←h₁] at h₄
          apply Primrec.bdMu_eval_gt at h₄
          simp at h₄
          simp [Nat.sub_eq_zero_iff_le] at h₄
          apply h₄.antisymm at h₃
          exact ih h₃

theorem bd_zero_of_not_dom : ¬ (f v).Dom → ∀ k, bd f (k ∷ᵥ v) = 0 := by
  intro h₁
  by_contra h₂
  simp at h₂; rcases h₂ with ⟨k, h₂⟩
  exact h₁ (Part.dom_of_mem (bd_sound (Nat.sub_add_cancel (pos_of_ne_zero h₂)).symm))

theorem bd_pos_of_mem : m ∈ f v → ∃ k, bd f (k ∷ᵥ v) = m + 1 := by
  intro h
  suffices ∃ k, ∀ k' ≥ k, bd f (k' ∷ᵥ v) = m + 1 by
    rcases this with ⟨k, this⟩
    exact ⟨k, this k (le_refl k)⟩
  induction f generalizing m with (simp [bd]; try simp at h)
  | const | succ | proj => simp [Vec.head, h]
  | comp f g ih₁ ih₂ =>
    rcases h with ⟨w, h₁, h₂⟩
    choose u h₁ using λ i => ih₂ i (h₁ i)
    rcases ih₁ h₂ with ⟨k, h₂⟩
    exists max (Vec.max u) k
    intro k' hk; simp at hk
    have := λ i => h₁ i k' ((Vec.le_max i).trans hk.1)
    simp_vec; simp [this]
    exact h₂ k' hk.2
  | prec f g ih₁ ih₂ =>
    rw [Vec.eq_cons v] at h; simp [Vec.head] at h
    generalize v 0 = a, v.tail = v at h ⊢
    induction a generalizing m with
    | zero =>
      simp [prec_eval_zero] at h
      simp [Primrec.prec_eval_zero]
      rcases ih₁ h with ⟨k, h⟩
      exists k
    | succ a ih =>
      simp [prec_eval_succ] at h
      rcases h with ⟨b, h₁, h₂⟩
      apply ih at h₁; rcases h₁ with ⟨k₁, h₁⟩
      apply ih₂ at h₂; rcases h₂ with ⟨k₂, h₂⟩
      simp [Primrec.prec_eval_succ]
      exists max k₁ k₂
      intro k' hk; simp at hk
      simp [h₁ k' hk.1]; simp_vec
      exact h₂ k' hk.2
  | mu f ih =>
    simp [Part.mem_find_iff, Part.pos_iff] at h
    rcases h with ⟨⟨a, h₁, ha⟩, h₂⟩
    apply ih at h₁; rcases h₁ with ⟨k, h₁⟩
    choose u h₂ using λ k : Fin m => ih (h₂ k k.isLt)
    exists max (Vec.max u) (max (m + 1) k)
    intro k' hk; simp [Nat.succ_le_iff] at hk
    generalize h₄ : Primrec.bdMu _ _ = k''
    simp_vec at h₄
    have : k'' = m := by
      subst h₄
      apply Primrec.bdMu_eval_eq
      · exact hk.2.1.le
      · intro k'' hk'
        specialize h₂ ⟨k'', hk'⟩ k' ((Vec.le_max _).trans hk.1)
        simp at h₂; simp [h₂]
      · simp [h₁ k' hk.2.2]; exact ha
    subst this; simp [hk.2.1]
    intro k''' hk'
    specialize h₂ ⟨k''', hk'⟩ k' ((Vec.le_max _).trans hk.1); simp at h₂
    simp [h₂]

theorem bd_of_mem : m ∈ f v → ∃ k, ∀ k', bd f (k' ∷ᵥ v) = if k' < k then 0 else m + 1 := by
  intro h
  apply bd_pos_of_mem at h
  exists Nat.find h
  intro k
  split
  next h' =>
    apply Nat.find_min at h'
    cases h'' : f.bd (k ∷ᵥ v) with simp
    | succ m' =>
      rcases h with ⟨k', h⟩
      cases Nat.le_or_ge k k' with
      | inl hk => apply bd_mono h'' at hk; simp [h] at hk; simp [hk] at h'; contradiction
      | inr hk => apply bd_mono h at hk; simp [h''] at hk; simp [hk] at h''; contradiction
  next h' =>
    simp at h'
    rcases h' with ⟨k', hk, h'⟩
    exact bd_mono h' hk

theorem bd_ofPrim {f : Primrec n} : (ofPrim f).bd (k ∷ᵥ v) = f v + 1 := by
  induction f with simp [Vec.head, ofPrim, bd]
  | comp f g ih₁ ih₂ =>
    simp_vec; simp [ih₁, ih₂]
  | prec f g ih₁ ih₂ =>
    rw [Vec.eq_cons v]; simp [Vec.head]
    generalize v 0 = a, v.tail = v
    induction a with
    | zero => simp [Primrec.prec_eval_zero, ih₁]
    | succ a ih => simp [Primrec.prec_eval_succ, ih]; simp_vec; simp [ih₂]

theorem dom_iff_exists_bd_pos : (f v).Dom ↔ ∃ k, 0 < bd f (k ∷ᵥ v) := by
  by_cases h : (f v).Dom <;> simp [h]
  · rcases bd_pos_of_mem (Part.get_mem h) with ⟨k, h'⟩
    exists k; simp [h']
  · simp [bd_zero_of_not_dom h]

/--
  Short-circuit if-then-else.
  `site f g h` is equivalent to `g` when `f` is positive, and equivalent to `h` when `f` is zero.
  -/
def site (f g h : Partrec n) : Partrec n :=
  let k := mu (Primrec.cond.toPart.comp₃ (f.comp (proj ·.succ)) g.bd.toPart h.bd.toPart)
  Primrec.cond.toPart.comp₃ f
    (Primrec.pred.toPart.comp₁ (g.bd.toPart.comp (k ∷ᵥ proj)))
    (Primrec.pred.toPart.comp₁ (h.bd.toPart.comp (k ∷ᵥ proj)))

theorem mem_site_eval_iff : m ∈ site f g h v ↔ 0 < f v ∧ m ∈ g v ∨ 0 ∈ f v ∧ m ∈ h v := by
  simp [site, Fin.forall_fin_succ, Part.pos_iff]
  constructor
  · rintro ⟨a, _, _, ⟨h₁, ⟨_, h₂, rfl⟩, _, h₃, rfl⟩, hm⟩
    simp [Vec.exists_vec_succ] at h₂ h₃
    rcases h₂ with ⟨k, _, ⟨h₂, h₂'⟩, rfl⟩
    rcases h₃ with ⟨_, _, ⟨h₃, h₃'⟩, rfl⟩
    simp [←Vec.ext_iff] at h₂' h₃'; subst h₂' h₃'
    apply Part.mem_unique h₂ at h₃; subst h₃
    simp [Part.mem_find_iff, ←Vec.ext_iff] at h₂
    rcases h₂ with ⟨⟨_, h₂, h₃⟩, h₄⟩
    apply Part.mem_unique h₁ at h₂; subst h₂
    split at hm
    next ha =>
      simp [ha] at h₃
      left; exists ⟨_, h₁, ha⟩
      simp [hm]; apply bd_sound (k := k); simp [Nat.sub_add_cancel h₃]
    next ha =>
      simp at ha; subst ha; simp at h₃
      right; exists h₁
      simp [hm]; apply bd_sound (k := k); simp [Nat.sub_add_cancel h₃]
  · rintro (⟨⟨a, h₁, h₂⟩, h₃⟩ | ⟨h₁, h₂⟩)
    · apply bd_of_mem at h₃; rcases h₃ with ⟨k, h₃⟩
      refine ⟨a, m, h.bd (k ∷ᵥ v) - 1, ⟨h₁, ⟨m + 1, ⟨k ∷ᵥ v, ⟨?goal1, ?_⟩, ?_⟩, ?_⟩,
        h.bd (k ∷ᵥ v), ⟨k ∷ᵥ v, ⟨?goal1, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> simp [h₂, h₃]
      simp [Part.mem_find_iff, ←Vec.ext_iff]
      constructor
      · exists a; simp [h₁, h₂]
      · intro k' hk; exists a; simp [hk, h₁, h₂]
    · apply bd_of_mem at h₂; rcases h₂ with ⟨k, h₂⟩
      refine ⟨0, g.bd (k ∷ᵥ v) - 1, m, ⟨h₁, ⟨g.bd (k ∷ᵥ v), ⟨k ∷ᵥ v, ⟨?goal2, ?_⟩, ?_⟩, ?_⟩,
        m + 1, ⟨k ∷ᵥ v, ⟨?goal2, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> simp [h₂]
      simp [Part.mem_find_iff, ←Vec.ext_iff]
      constructor
      · exists 0; simp [h₁, h₂]
      · intro k' hk; exists 0; simp [hk, h₁, h₂]

theorem site_dom : (site f g h v).Dom ↔ 0 < f v ∧ (g v).Dom ∨ 0 ∈ f v ∧ (h v).Dom := by
  simp [Part.dom_iff_mem, mem_site_eval_iff]; aesop

/-- Short-circuit and. -/
def sand (f g : Partrec n) := site f g (const 0)

theorem sand_dom : (sand f g v).Dom ↔ 0 < f v ∧ (g v).Dom ∨ 0 ∈ f v := by
  simp [sand, site_dom]

theorem sand_eval_pos_iff : 0 < sand f g v ↔ 0 < f v ∧ 0 < g v := by
  conv => lhs; simp [Part.pos_iff]; simp [sand, mem_site_eval_iff]
  constructor
  · rintro ⟨_, (⟨h₁, h₂⟩ | ⟨_, rfl⟩), h₃⟩
    · exists h₁; simp [Part.pos_iff]; exact ⟨_, h₂, h₃⟩
    · contradiction
  · intro ⟨h₁, h₂⟩
    simp [Part.pos_iff] at h₂
    rcases h₂ with ⟨_, h₂, h₃⟩
    exact ⟨_, Or.inl ⟨h₁, h₂⟩, h₃⟩

theorem sand_eval_zero_iff : 0 ∈ sand f g v ↔ 0 < f v ∧ 0 ∈ g v ∨ 0 ∈ f v := by
  simp [sand, mem_site_eval_iff]

/-- Parallel execution of `f` and `g`. -/
def par (f g : Partrec n) : Partrec n :=
  let k := mu (ofPrim (.or f.bd g.bd))
  site (f.bd.toPart.comp (k ∷ᵥ proj))
    (Primrec.pred.toPart.comp₁ (f.bd.toPart.comp (k ∷ᵥ proj)))
    (Primrec.pred.toPart.comp₁ (g.bd.toPart.comp (k ∷ᵥ proj)))

theorem par_dom : (par f g v).Dom ↔ (f v).Dom ∨ (g v).Dom := by
  simp [par, site_dom, Fin.forall_fin_succ, Part.find_dom, Part.mem_find_iff, eq_comm (a := 0)]
  constructor
  · rintro (⟨⟨w, ⟨⟨(h | h), _⟩, _⟩, _⟩, _⟩ | ⟨_, ⟨_, (h | h)⟩⟩)
      <;> [left; right; left; right] <;> simp [dom_iff_exists_bd_pos] <;> exact ⟨_, h⟩
  · intro h
    by_cases h₁ : (f v).Dom
    · apply Part.get_mem at h₁; apply bd_of_mem at h₁; rcases h₁ with ⟨k₁, h₁⟩
      by_cases h₂ : (g v).Dom
      · apply Part.get_mem at h₂; apply bd_of_mem at h₂; rcases h₂ with ⟨k₂, h₂⟩
        by_cases h₃ : k₁ ≤ k₂
        · left; refine ⟨⟨k₁ ∷ᵥ v, ?_⟩, ⟨k₁, ?_⟩⟩ <;> simp [h₁, h₂]
          exact λ _ h => ⟨h, h.trans_le h₃⟩
        · right; refine ⟨⟨k₂ ∷ᵥ v, ?_⟩, ⟨k₂, ?_⟩⟩ <;> simp [h₁, h₂]
          simp at h₃; exact ⟨λ _ h => ⟨h.trans h₃, h⟩, h₃⟩
      · apply bd_zero_of_not_dom at h₂
        left; refine ⟨⟨k₁ ∷ᵥ v, ?_⟩, ⟨k₁, ?_⟩⟩ <;> simp [h₁, h₂]
    · simp [h₁] at h
      apply bd_zero_of_not_dom at h₁
      apply Part.get_mem at h; apply bd_of_mem at h; rcases h with ⟨k₂, h₂⟩
      right; refine ⟨⟨k₂ ∷ᵥ v, ?_⟩, ⟨k₂, ?_⟩⟩ <;> simp [h₁, h₂]

theorem mem_par_eval_left : m ∈ f v → ¬ (g v).Dom → m ∈ par f g v := by
  intro h₁ h₂
  apply bd_of_mem at h₁; rcases h₁ with ⟨k₁, h₁⟩
  apply bd_zero_of_not_dom at h₂
  simp [par, mem_site_eval_iff, Fin.forall_fin_succ, Part.mem_find_iff, eq_comm (a := 0)]
  left; refine ⟨⟨k₁ ∷ᵥ v, ?_⟩, ⟨m + 1, ⟨k₁ ∷ᵥ v, ?_⟩, ?_⟩⟩ <;> simp [h₁, h₂]

theorem mem_par_eval_right : ¬ (f v).Dom → m ∈ g v → m ∈ par f g v := by
  intro h₁ h₂
  apply bd_zero_of_not_dom at h₁
  apply bd_of_mem at h₂; rcases h₂ with ⟨k₂, h₂⟩
  simp [par, mem_site_eval_iff, Fin.forall_fin_succ, Part.mem_find_iff, eq_comm (a := 0)]
  right; refine ⟨⟨k₂ ∷ᵥ v, ?_⟩, ⟨m + 1, ⟨k₂ ∷ᵥ v, ?_⟩, ?_⟩⟩ <;> simp [h₁, h₂]

theorem mem_par_eval : m ∈ par f g v → m ∈ f v ∨ m ∈ g v := by
  intro h
  simp [par, mem_site_eval_iff, Fin.forall_fin_succ, Vec.exists_vec_succ, ←Vec.ext_iff, eq_comm (a := 0)] at h
  rcases h with ⟨⟨k, h₁, h₂⟩, _, ⟨_, h₃, rfl⟩, rfl⟩ | ⟨⟨k, h₁, h₂⟩, _, ⟨_, h₃, rfl⟩, rfl⟩
  · apply Part.mem_unique h₁ at h₃; subst h₃
    left; apply bd_sound (k := k)
    simp [Nat.sub_add_cancel h₂]
  · apply Part.mem_unique h₁ at h₃; subst h₃
    simp [Part.mem_find_iff, h₂] at h₁
    right; apply bd_sound (k := k)
    simp [Nat.sub_add_cancel h₁.1]

open Lean.Parser Std in
def repr : Partrec n → ℕ → Format
| const n, _ => "const " ++ n.repr
| succ, _ => "succ"
| proj i, p => Repr.addAppParen ("proj " ++ reprPrec i maxPrec) p
| comp f v, p => Repr.addAppParen ("comp " ++ repr f maxPrec ++ " " ++ Format.bracketFill "[" (Format.joinSep (Vec.toList λ i => (v i).repr 0) (", ")) "]ᵥ") p
| prec f g, p => Repr.addAppParen ("prec " ++ repr f maxPrec ++ " " ++ repr g maxPrec) p
| mu f, p => Repr.addAppParen ("mu " ++ repr f maxPrec) p

instance : Repr (Partrec n) := ⟨repr⟩

end Partrec

variable {α : Type u} [Encodable α] {s : Set α}

/--
  A set is recursive if it can be decided by a recursive function `f`.
  
  Note: for flexibility, we only require `f`'s totality on the image of `Encodable.encode`, instead
  of the whole `ℕ`.
  -/
class Recursive (s : Set α) where
  char : Partrec 1
  char_dom : ∀ (x : α), (char [Encodable.encode x]ᵥ).Dom
  mem_iff : ∀ x, x ∈ s ↔ 0 < char [Encodable.encode x]ᵥ

namespace Recursive

variable [Recursive s]

theorem not_mem_iff (x : α) :
  x ∉ s ↔ 0 ∈ char s [Encodable.encode x]ᵥ := by
  rw [mem_iff x, ←Part.some_get (char_dom x)]
  simp [Part.zero_def, eq_comm, -Part.some_get]

def compl : Recursive sᶜ where
  char := (Primrec.nsign.toPart).comp₁ (char s)
  char_dom x := by simp; exact char_dom x
  mem_iff x := by simp; simp [not_mem_iff, Part.zero_def, Part.eq_some_iff]

instance dec (s : Set α) [Recursive s] (x : α) : Decidable (x ∈ s) := by
  simp [mem_iff x]
  rw [←Part.some_get (char_dom x)]
  simp [Part.zero_def, -Part.some_get]
  infer_instance

end Recursive

/-- `Prop` version of `Recursive`. -/
def IsRecursive (s : Set α) := Nonempty (Recursive s)

theorem IsRecursive.def : IsRecursive s ↔
  ∃ (f : Partrec 1), (∀ x : α, (f [Encodable.encode x]ᵥ).Dom) ∧ ∀ x, x ∈ s ↔ 0 < f [Encodable.encode x]ᵥ := by
  constructor
  · intro ⟨⟨f, _, _⟩⟩; exists f
  · intro ⟨f, h₁, h₂⟩; exact ⟨⟨f, h₁, h₂⟩⟩

theorem IsRecursive.compl_iff : IsRecursive s ↔ IsRecursive sᶜ := by
  constructor
  · intro ⟨h⟩; exact ⟨Recursive.compl⟩
  · intro ⟨h⟩; rw [←compl_compl s]; exact ⟨Recursive.compl⟩

/--
  A set is enumerable (also called recursively enumerable, or RE) if it can be decided through a
  "μ-operator search" over a recursive function. The equivalent definitions are
  `IsEnumerable.iff_range_partrec` and `IsEnumerable.iff_semi_decidable`. -/
class Enumerable (s : Set α) where
  enum : Partrec 2
  enum_dom : ∀ n (x : α), (enum [n, Encodable.encode x]ᵥ).Dom
  mem_iff : ∀ x, x ∈ s ↔ ∃ n, 0 < enum [n, Encodable.encode x]ᵥ

theorem Enumerable.not_mem_iff [Enumerable s] (x : α) :
  x ∉ s ↔ ∀ n, 0 ∈ enum s [n, Encodable.encode x]ᵥ := by
  rw [mem_iff x]; simp
  congr! with n
  rw [←Part.some_get (enum_dom n x)]
  simp [Part.zero_def, eq_comm, -Part.some_get]

instance Recursive.enumerable [Recursive s] : Enumerable s where
  enum := (char s).comp₁ (.proj 1)
  enum_dom n x := by simp [Vec.eq_one]; exact char_dom x
  mem_iff x := by simp [Vec.eq_one]; exact mem_iff x

/-- `Prop` version of `Enumerable`. -/
def IsEnumerable (s : Set α) := Nonempty (Enumerable s)

theorem IsRecursive.enumerable : IsRecursive s → IsEnumerable s := by
  intro ⟨h⟩; exact ⟨h.enumerable⟩

theorem IsEnumerable.def : IsEnumerable s ↔
  ∃ (f : Partrec 2), (∀ n (x : α), (f [n, Encodable.encode x]ᵥ).Dom) ∧ ∀ x, x ∈ s ↔ ∃ n, 0 < f [n, Encodable.encode x]ᵥ := by
  constructor
  · intro ⟨⟨f, _, _⟩⟩; exists f
  · intro ⟨f, h₁, h₂⟩; exact ⟨⟨f, h₁, h₂⟩⟩

/-- A set is enumerable if and only if it is the range of some partial recursive function `f`. -/
theorem IsEnumerable.iff_range_partrec :
  IsEnumerable s ↔ ∃ (f : Partrec 1), ∀ x, x ∈ s ↔ ∃ n, Encodable.encode x ∈ f [n]ᵥ := by
  constructor
  · intro ⟨⟨f, h₁, h₂⟩⟩
    exists .site (f.comp₂ (.ofPrim .fst) (.ofPrim .snd)) (.ofPrim .snd) .loop
    intro x; simp [h₂, Partrec.mem_site_eval_iff]
    constructor
    · intro ⟨n, h⟩
      exists n.pair (Encodable.encode x)
      simp [h]
    · intro ⟨n, h, h'⟩
      exists n.unpair.1
      simp [h, h']
  · intro ⟨f, h⟩
    refine ⟨⟨.ofPrim (.eq
      (f.bd.comp₂ (Primrec.fst.comp₁ (.proj 0)) (Primrec.snd.comp₁ (.proj 0)))
      (Primrec.succ.comp₁ (.proj 1))), ?_, ?_⟩⟩
    · simp
    · intro x
      simp [h]
      constructor
      · intro ⟨n, h'⟩
        apply Partrec.bd_pos_of_mem at h'
        rcases h' with ⟨k, h'⟩
        exists k.pair n; simp [h']
      · intro ⟨n, h'⟩
        apply Partrec.bd_sound at h'
        exists n.unpair.2

/-- A set is enumerable if and only if it can be semi-decided. -/
theorem IsEnumerable.iff_semi_decidable :
  IsEnumerable s ↔ ∃ (f : Partrec 1), ∀ x, x ∈ s ↔ (f [Encodable.encode x]ᵥ).Dom := by
  constructor
  · intro ⟨⟨f, h₁, h₂⟩⟩
    exists .mu f
    intro x
    rw [h₂]; simp [Part.find_dom, h₁]
  · intro ⟨f, h⟩
    refine ⟨⟨.ofPrim f.bd, ?_, ?_⟩⟩ <;> simp [h, Partrec.dom_iff_exists_bd_pos]

/-- A set is recursive if and only if it and its complement are both enumerable. -/
theorem IsRecursive.iff_re_compl_re : IsRecursive s ↔ IsEnumerable s ∧ IsEnumerable sᶜ := by
  constructor
  · intro h
    exact ⟨h.enumerable, (IsRecursive.compl_iff.mp h).enumerable⟩
  · intro ⟨h₁, h₂⟩
    rw [IsEnumerable.iff_semi_decidable] at h₁ h₂
    rcases h₁ with ⟨f, h₁⟩
    rcases h₂ with ⟨g, h₂⟩; simp at h₂
    refine ⟨⟨.par ((Partrec.const 1).comp₁ f) ((Partrec.const 0).comp₁ g), ?_, ?_⟩⟩
    · intro x; simp [Partrec.par_dom]
      by_cases h : x ∈ s <;> [rw [h₁] at h; rw [h₂] at h] <;> simp [h]
    · intro x
      by_cases h : x ∈ s <;> simp [h, Part.pos_iff]
      · exists 1; simp
        apply Partrec.mem_par_eval_left
        · simp [←Part.dom_iff_mem, ←h₁, h]
        · simp [←h₂, h]
      · intro a h'
        apply Partrec.mem_par_eval at h'
        rcases h' with h' | h' <;> simp at h' <;> rcases h' with ⟨h', rfl⟩ <;> simp
        simp [←Part.dom_iff_mem, ←h₁, h] at h'
