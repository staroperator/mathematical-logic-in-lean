import MathematicalLogic.FirstOrder.Proof
import MathematicalLogic.FirstOrder.Semantics

section

variable (r : α → α → Prop) [IsTrans α r] [IsDirected α r]

lemma directed_of_vec [h : Nonempty α] (v : Vec α n) : ∃ a, ∀ i, r (v i) a := by
  induction n with
  | zero => rcases h with ⟨a⟩; exists a; exact (·.elim0)
  | succ n ih =>
    rcases @ih v.tail with ⟨i, h₁⟩
    rcases directed_of r i v.head with ⟨j, h₂, h₃⟩
    exists j
    intro i
    cases i using Fin.cases with
    | zero => exact h₃
    | succ i => exact Trans.trans (h₁ i) h₂

lemma directed_of_three (x y z : α) : ∃ a, r x a ∧ r y a ∧ r z a := by
  rcases directed_of r x y with ⟨a, h₁, h₂⟩
  rcases directed_of r a z with ⟨b, h₃, h₄⟩
  exact ⟨b, Trans.trans h₁ h₃, Trans.trans h₂ h₃, h₄⟩

end

namespace FirstOrder.Language

universe u v w

structure Hom (L₁ L₂ : Language) where
  onFunc : ∀ {n}, L₁.Func n → L₂.Func n
  onRel : ∀ {n}, L₁.Rel n → L₂.Rel n
infix:50 " →ᴸ " => Hom

namespace Hom

variable {L L₁ L₂ L₃ : Language} {φ : L₁ →ᴸ L₂}

@[ext] theorem ext
  (h₁ : ∀ n (f : L₁.Func n), φ.onFunc f = ψ.onFunc f)
  (h₂ : ∀ n (r : L₁.Rel n), φ.onRel r = ψ.onRel r) : φ = ψ := by
  cases φ; cases ψ; simp
  constructor <;> funext <;> apply_assumption

@[simps] def id : L →ᴸ L where
  onFunc f := f
  onRel r := r

@[simps] def comp (φ₂ : L₂ →ᴸ L₃) (φ₁ : L₁ →ᴸ L₂) : L₁ →ᴸ L₃ where
  onFunc f := φ₂.onFunc (φ₁.onFunc f)
  onRel r := φ₂.onRel (φ₁.onRel r)
infixl:90 " ∘ᴸ " => comp

theorem comp_id : φ ∘ᴸ id = φ := by ext <;> simp
theorem id_comp : id ∘ᴸ φ = φ := by ext <;> simp
theorem comp_assoc : φ₃ ∘ᴸ φ₂ ∘ᴸ φ₁ = φ₃ ∘ᴸ (φ₂ ∘ᴸ φ₁) := by ext <;> simp

def onTerm (φ : L₁ →ᴸ L₂) : L₁.Term n → L₂.Term n
| #x => #x
| f ⬝ᶠ v => φ.onFunc f ⬝ᶠ λ i => φ.onTerm (v i)

theorem id_onTerm : id.onTerm t = t := by
  induction t with simp [onTerm]
  | func f v ih => ext; apply ih

theorem comp_onTerm : (φ₂ ∘ᴸ φ₁).onTerm t = φ₂.onTerm (φ₁.onTerm t) := by
  induction t with simp [onTerm]
  | func f v ih => ext; apply ih

theorem onTerm_subst : φ.onTerm (t[σ]ₜ) = (φ.onTerm t)[φ.onTerm ∘ σ]ₜ := by
  induction t with simp [onTerm]
  | func f v ih => ext; apply ih

theorem onTerm_shift : φ.onTerm (↑ₜt) = ↑ₜ(φ.onTerm t) := by
  simp [Term.shift, onTerm_subst]; rfl

def onFormula (φ : L₁ →ᴸ L₂) : L₁.Formula n → L₂.Formula n
| r ⬝ʳ v => φ.onRel r ⬝ʳ λ i => φ.onTerm (v i)
| t₁ ≐ t₂ => φ.onTerm t₁ ≐ φ.onTerm t₂
| ⊥ => ⊥
| p ⇒ q => φ.onFormula p ⇒ φ.onFormula q
| ∀' p => ∀' (φ.onFormula p)

theorem onFormula_neg : φ.onFormula (~ p) = ~ φ.onFormula p := rfl

theorem onFormula_and : φ.onFormula (p ⩑ q) = φ.onFormula p ⩑ φ.onFormula q := rfl

theorem onFormula_andN {v : Vec (L₁.Formula n) m} : φ.onFormula (⋀ i, v i) = ⋀ i, φ.onFormula (v i) := by
  induction m with try simp [onFormula, onFormula_and, Formula.andN]
  | zero => rfl
  | succ m ih => simp [ih]; rfl

theorem id_onFormula : id.onFormula p = p := by
  induction p with simp [onFormula]
  | rel r v => ext; simp [id_onTerm]
  | eq t₁ t₂ => simp [id_onTerm]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => simp [ih]

theorem comp_onFormula : (φ₂ ∘ᴸ φ₁).onFormula p = φ₂.onFormula (φ₁.onFormula p) := by
  induction p with simp [onFormula]
  | rel r v => ext; simp [comp_onTerm]
  | eq t₁ t₂ => simp [comp_onTerm]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => simp [ih]

theorem onFormula_subst {σ : L₁.Subst n m} : φ.onFormula (p[σ]ₚ) = (φ.onFormula p)[φ.onTerm ∘ σ]ₚ := by
  induction p generalizing m with simp [onFormula]
  | rel r v => ext; simp [onTerm_subst]
  | eq t₁ t₂ => simp [onTerm_subst]
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih =>
    simp [ih]; congr; funext x; cases x using Fin.cases <;> simp [onTerm, onTerm_shift]

theorem onFormula_shift : φ.onFormula (↑ₚp) = ↑ₚ(φ.onFormula p) := by
  simp [Formula.shift, onFormula_subst]; rfl

theorem onFormula_subst_single : φ.onFormula (p[↦ₛ t]ₚ) = (φ.onFormula p)[↦ₛ (φ.onTerm t)]ₚ := by
  simp [onFormula_subst]; congr; funext x; cases x using Fin.cases <;> rfl

theorem on_axiom : p ∈ L₁.Axiom → φ.onFormula p ∈ L₂.Axiom := by
  intro h
  induction h <;> simp [onFormula, onFormula_subst_single, onFormula_shift, onFormula_andN]
  case all ih => exact .all ih
  all_goals constructor

theorem on_proof : Γ ⊢ p → φ.onFormula '' Γ ⊢ φ.onFormula p := by
  intro h
  induction h with
  | hyp h => exact .hyp ⟨_, h, rfl⟩
  | ax h => exact .ax (on_axiom h)
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

@[simps] def reduct (φ : L₁ →ᴸ L₂) (M : L₂.Structure) : L₁.Structure where
  Dom := M
  interpFunc f v := M.interpFunc (φ.onFunc f) v
  interpRel r v := M.interpRel (φ.onRel r) v

variable {M : L₂.Structure}

theorem interp_onTerm : ⟦ φ.onTerm t ⟧ₜ M, ρ = ⟦ t ⟧ₜ φ.reduct M, ρ := by
  induction t with simp [onTerm]
  | func f v ih => congr; funext; apply ih

theorem satisfy_onFormula : M ⊨[ρ] φ.onFormula p ↔ φ.reduct M ⊨[ρ] p := by
  induction p with simp [onFormula]
  | rel | eq => simp [interp_onTerm] <;> rfl
  | imp p q ih₁ ih₂ => simp [ih₁, ih₂]
  | all p ih => simp [ih]

theorem on_satisfiable : Satisfiable.{u} (φ.onFormula '' Γ) → Satisfiable.{u} Γ := by
  intro ⟨M, ρ, h₁⟩
  exists φ.reduct M, ρ
  intro p h₂
  rw [←satisfy_onFormula]
  apply h₁
  exists p   

end Hom



variable {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)]

structure DirectedSystem (L : ι → Language) where
  hom : ∀ i j, i ≤ j → L i →ᴸ L j
  hom_id : ∀ {i} h, hom i i h = .id
  hom_comp : ∀ {i j k} h₁ h₂ h₃, hom j k h₂ ∘ᴸ hom i j h₁ = hom i k h₃

namespace DirectedSystem

variable {L : ι → Language} (φ : DirectedSystem L)

def setoidFunc (n) : Setoid (Σ i, (L i).Func n) where
  r := λ ⟨i, f⟩ ⟨j, g⟩ =>
    ∃ k, ∃ (h₁ : i ≤ k) (h₂ : j ≤ k), (φ.hom i k h₁).onFunc f = (φ.hom j k h₂).onFunc g
  iseqv.refl := λ ⟨i, f⟩ => by exists i, le_refl i, le_refl i
  iseqv.symm := @λ ⟨i, f⟩ ⟨j, g⟩ ⟨k, h₁, h₂, h₃⟩ => by
    exists k, h₂, h₁; rw [h₃]
  iseqv.trans := @λ ⟨i, f⟩ ⟨j, g⟩ ⟨k, h⟩ ⟨l₁, h₁, h₂, h₃⟩ ⟨l₂, h₁', h₂', h₃'⟩ => by
    rcases directed_of (· ≤ ·) l₁ l₂ with ⟨l, h₄, h₅⟩
    exists l, le_trans h₁ h₄, le_trans h₂' h₅
    rw [←φ.hom_comp h₁ h₄ _, ←φ.hom_comp h₂' h₅]
    simp [h₃, ←h₃']
    simp_rw [←Hom.comp_onFunc]
    rw [φ.hom_comp _ _ (le_trans h₂ h₄), φ.hom_comp _ _ (le_trans h₂ h₄)]

def setoidRel (n) : Setoid (Σ i, (L i).Rel n) where
  r := λ ⟨i, r⟩ ⟨j, s⟩ =>
    ∃ k, ∃ (h₁ : i ≤ k) (h₂ : j ≤ k), (φ.hom i k h₁).onRel r = (φ.hom j k h₂).onRel s
  iseqv.refl := λ ⟨i, r⟩ => by exists i, le_refl i, le_refl i
  iseqv.symm := @λ ⟨i, r⟩ ⟨j, s⟩ ⟨k, h₁, h₂, h₃⟩ => by
    exists k, h₂, h₁; rw [h₃]
  iseqv.trans := @λ ⟨i, r⟩ ⟨j, s⟩ ⟨k, t⟩ ⟨l₁, h₁, h₂, h₃⟩ ⟨l₂, h₁', h₂', h₃'⟩ => by
    rcases directed_of (· ≤ ·) l₁ l₂ with ⟨l, h₄, h₅⟩
    exists l, le_trans h₁ h₄, le_trans h₂' h₅
    rw [←φ.hom_comp h₁ h₄ _, ←φ.hom_comp h₂' h₅]
    simp [h₃, ←h₃']
    simp_rw [←Hom.comp_onRel]
    rw [φ.hom_comp _ _ (le_trans h₂ h₄), φ.hom_comp _ _ (le_trans h₂ h₄)]

def directLimit : Language where
  Func n := Quotient (φ.setoidFunc n)
  Rel n := Quotient (φ.setoidRel n)

def homLimit (i : ι) : L i →ᴸ φ.directLimit where
  onFunc f := ⟦⟨i, f⟩⟧
  onRel r := ⟦⟨i, r⟩⟧

variable {φ : DirectedSystem L}

theorem homLimit_comp_hom {h : i ≤ j} : φ.homLimit j ∘ᴸ φ.hom i j h = φ.homLimit i := by
  ext <;> simp [homLimit] <;> apply Quotient.sound <;> exists j, le_refl j, h
    <;> simp [←Hom.comp_onFunc, ←Hom.comp_onRel] <;> rw [φ.hom_comp]

theorem term_hom_eq_of_homLimit_eq [Nonempty ι] (t₁ : (L i).Term n) (t₂ : (L j).Term n)
  (h : (φ.homLimit i).onTerm t₁ = (φ.homLimit j).onTerm t₂) :
  ∃ k h₁ h₂, (φ.hom i k h₁).onTerm t₁ = (φ.hom j k h₂).onTerm t₂ := by
  generalize h' : (φ.homLimit j).onTerm t₂ = t at h
  induction t generalizing t₁ t₂ with
  | var x =>
    cases t₁ <;> simp [Hom.onTerm] at h
    cases t₂ <;> simp [Hom.onTerm] at h'
    simp [h, h', Hom.onTerm]
    exact directed_of (· ≤ ·) i j
  | func f v ih =>
    cases t₁ <;> simp [Hom.onTerm] at h; rcases h with ⟨h, h₁, h₂⟩; subst h; simp at h₁ h₂
    cases t₂ <;> simp [Hom.onTerm] at h'; rcases h' with ⟨h', h₃, h₄⟩; subst h'; simp at h₃ h₄
    rcases Quotient.exact' (h₁.trans h₃.symm) with ⟨k₁, h₅, h₅', h₅''⟩
    choose u h₆ h₆' h₆'' using λ i => ih i _ _ (congr_fun h₄ i) (congr_fun h₂ i)
    rcases directed_of_vec (α := ι) (· ≤ ·) u with ⟨k₂, h₇⟩
    rcases directed_of (· ≤ ·) k₁ k₂ with ⟨k, h₈, h₈'⟩
    exists k, h₅.trans h₈, h₅'.trans h₈
    simp [Hom.onTerm]; constructor
    · rw [←φ.hom_comp h₅ h₈, ←φ.hom_comp h₅' h₈]; simp [h₅'']
    · ext x; rw [←φ.hom_comp (h₆ x) ((h₇ x).trans h₈'), ←φ.hom_comp (h₆' x) ((h₇ x).trans h₈')]; simp [Hom.comp_onTerm, h₆'']

theorem formula_hom_eq_of_homLimit_eq [Nonempty ι] (p : (L i).Formula n) (q : (L j).Formula n)
  (h : (φ.homLimit i).onFormula p = (φ.homLimit j).onFormula q) :
  ∃ k h₁ h₂, (φ.hom i k h₁).onFormula p = (φ.hom j k h₂).onFormula q := by
  generalize h' : (φ.homLimit j).onFormula q = r at h
  induction r with
  | rel r v =>
    cases p <;> simp [Hom.onFormula] at h; rcases h with ⟨h, h₁, h₂⟩; subst h; simp at h₁ h₂
    cases q <;> simp [Hom.onFormula] at h'; rcases h' with ⟨h', h₃, h₄⟩; subst h'; simp at h₃ h₄
    rcases Quotient.exact' (h₁.trans h₃.symm) with ⟨k₁, h₅, h₅', h₅''⟩
    choose u h₆ h₆' h₆'' using λ i => term_hom_eq_of_homLimit_eq _ _ ((congr_fun h₂ i).trans (congr_fun h₄ i).symm)
    rcases directed_of_vec (α := ι) (· ≤ ·) u with ⟨k₂, h₇⟩
    rcases directed_of (· ≤ ·) k₁ k₂ with ⟨k, h₈, h₈'⟩
    exists k, h₅.trans h₈, h₅'.trans h₈
    simp [Hom.onFormula]; constructor
    · rw [←φ.hom_comp h₅ h₈, ←φ.hom_comp h₅' h₈]; simp [h₅'']
    · ext x; rw [←φ.hom_comp (h₆ x) ((h₇ x).trans h₈'), ←φ.hom_comp (h₆' x) ((h₇ x).trans h₈')]; simp [Hom.comp_onTerm, h₆'']
  | eq t₁ t₂ =>
    cases p <;> simp [Hom.onFormula] at h; rcases h with ⟨h₁, h₁'⟩
    cases q <;> simp [Hom.onFormula] at h'; rcases h' with ⟨h₂, h₂'⟩
    rcases term_hom_eq_of_homLimit_eq _ _ (h₁.trans h₂.symm) with ⟨k₁, h₃, h₃', h₃''⟩
    rcases term_hom_eq_of_homLimit_eq _ _ (h₁'.trans h₂'.symm) with ⟨k₂, h₄, h₄', h₄''⟩
    rcases directed_of (· ≤ ·) k₁ k₂ with ⟨k, h₅, h₅'⟩
    exists k, h₃.trans h₅, h₃'.trans h₅
    simp [Hom.onFormula]; constructor
    · rw [←φ.hom_comp h₃ h₅, ←φ.hom_comp h₃' h₅]; simp [Hom.comp_onTerm, h₃'']
    · rw [←φ.hom_comp h₄ h₅', ←φ.hom_comp h₄' h₅']; simp [Hom.comp_onTerm, h₄'']
  | false =>
    cases p <;> simp [Hom.onFormula] at h
    cases q <;> simp [Hom.onFormula] at h'
    simp [Hom.onFormula]
    exact directed_of (· ≤ ·) i j
  | imp r₁ r₂ ih₁ ih₂ =>
    cases p <;> simp [Hom.onFormula] at h; rcases h with ⟨h₁, h₁'⟩
    cases q <;> simp [Hom.onFormula] at h'; rcases h' with ⟨h₂, h₂'⟩
    rcases ih₁ _ _ h₂ h₁ with ⟨k₁, h₃, h₃', h₃''⟩
    rcases ih₂ _ _ h₂' h₁' with ⟨k₂, h₄, h₄', h₄''⟩
    rcases directed_of (· ≤ ·) k₁ k₂ with ⟨k, h₅, h₅'⟩
    exists k, h₃.trans h₅, h₃'.trans h₅
    simp [Hom.onFormula]; constructor
    · rw [←φ.hom_comp h₃ h₅, ←φ.hom_comp h₃' h₅]; simp [Hom.comp_onFormula, h₃'']
    · rw [←φ.hom_comp h₄ h₅', ←φ.hom_comp h₄' h₅']; simp [Hom.comp_onFormula, h₄'']
  | all r ih =>
    cases p <;> simp [Hom.onFormula] at h
    cases q <;> simp [Hom.onFormula] at h'
    simp [Hom.onFormula]
    rcases ih _ _ h' h with ⟨k, h₁, h₁', h₁''⟩
    exact ⟨k, h₁, h₁', h₁''⟩

theorem term_of_homLimit [h : Nonempty ι] (t : φ.directLimit.Term n) :
  ∃ i t', t = (φ.homLimit i).onTerm t' := by
  induction t with
  | var x => rcases h with ⟨i⟩; exists i, #x
  | @func m f v ih =>
    rcases f with ⟨i, f⟩
    choose u w ih using ih
    rcases directed_of_vec (α := ι) (· ≤ ·) u with ⟨j, h₁⟩
    rcases directed_of (· ≤ ·) i j with ⟨k, h₂, h₃⟩
    exists k, (φ.hom i k h₂).onFunc f ⬝ᶠ λ x => (φ.hom (u x) k (le_trans (h₁ x) h₃)).onTerm (w x)
    simp [Hom.onTerm]; constructor
    · simp [homLimit]; apply Quotient.sound
      exists k, h₂, le_refl k
      rw [←Hom.comp_onFunc, φ.hom_comp]
    · ext x; simp_rw [ih, ←Hom.comp_onTerm, homLimit_comp_hom]

theorem formula_of_homLimit [h : Nonempty ι] (p : φ.directLimit.Formula n) :
  ∃ i q, p = (φ.homLimit i).onFormula q := by
  induction p with
  | rel r v =>
    rcases r with ⟨i, r⟩
    choose u w h using λ x => term_of_homLimit (v x)
    rcases directed_of_vec (α := ι) (· ≤ ·) u with ⟨j, h₁⟩
    rcases directed_of (· ≤ ·) i j with ⟨k, h₂, h₃⟩
    exists k, (φ.hom i k h₂).onRel r ⬝ʳ λ x => (φ.hom (u x) k (le_trans (h₁ x) h₃)).onTerm (w x)
    simp [Hom.onFormula]; constructor
    · simp [homLimit]; apply Quotient.sound
      exists k, h₂, le_refl k
      rw [←Hom.comp_onRel, φ.hom_comp]
    · ext x; simp_rw [h, ←Hom.comp_onTerm, homLimit_comp_hom]
  | eq t₁ t₂ =>
    rcases term_of_homLimit t₁ with ⟨i, t₁', h₁⟩
    rcases term_of_homLimit t₂ with ⟨j, t₂', h₂⟩
    rcases directed_of (· ≤ ·) i j with ⟨k, h₃, h₄⟩
    exists k, (φ.hom i k h₃).onTerm t₁' ≐ (φ.hom j k h₄).onTerm t₂'
    simp [Hom.onFormula]
    constructor <;> rw [←Hom.comp_onTerm, homLimit_comp_hom] <;> assumption
  | false => rcases h with ⟨i⟩; exists i, ⊥
  | imp p q ih₁ ih₂ =>
    rcases ih₁ with ⟨i, p', h₁⟩
    rcases ih₂ with ⟨j, q', h₂⟩
    rcases directed_of (· ≤ ·) i j with ⟨k, h₃, h₄⟩
    exists k, (φ.hom i k h₃).onFormula p' ⇒ (φ.hom j k h₄).onFormula q'
    simp [Hom.onFormula]
    constructor <;> rw [←Hom.comp_onFormula, homLimit_comp_hom] <;> assumption
  | all p ih => rcases ih with ⟨i, q, h⟩; exists i, ∀' q; simp [Hom.onFormula, h]

theorem axiom_of_homLimit [Nonempty ι] (h : p ∈ φ.directLimit.Axiom) :
  ∃ i q, p = (φ.homLimit i).onFormula q ∧ q ∈ (L i).Axiom := by
  induction h with
  | @imp_self _ p₁ p₂ =>
    rcases formula_of_homLimit p₁ with ⟨i₁, q₁, h₁⟩
    rcases formula_of_homLimit p₂ with ⟨i₂, q₂, h₂⟩
    rcases directed_of (· ≤ ·) i₁ i₂ with ⟨i, h₃, h₄⟩
    let q₁' := (φ.hom i₁ i h₃).onFormula q₁
    let q₂' := (φ.hom i₂ i h₄).onFormula q₂
    exists i, q₁' ⇒ q₂' ⇒ q₁'
    constructor
    · simp [Hom.onFormula, q₁', q₂']; simp_rw [←Hom.comp_onFormula, homLimit_comp_hom]; simp [h₁, h₂]
    · exact .imp_self
  | @imp_distrib _ p₁ p₂ p₃ =>
    rcases formula_of_homLimit p₁ with ⟨i₁, q₁, h₁⟩
    rcases formula_of_homLimit p₂ with ⟨i₂, q₂, h₂⟩
    rcases formula_of_homLimit p₃ with ⟨i₃, q₃, h₃⟩
    rcases directed_of_three (α := ι) (· ≤ ·) i₁ i₂ i₃ with ⟨i, h₄, h₅, h₆⟩
    let q₁' := (φ.hom i₁ i h₄).onFormula q₁
    let q₂' := (φ.hom i₂ i h₅).onFormula q₂
    let q₃' := (φ.hom i₃ i h₆).onFormula q₃
    exists i, (q₁' ⇒ q₂' ⇒ q₃') ⇒ (q₁' ⇒ q₂') ⇒ q₁' ⇒ q₃'
    constructor
    · simp [Hom.onFormula, q₁', q₂', q₃']; simp_rw [←Hom.comp_onFormula, homLimit_comp_hom]; simp [h₁, h₂, h₃]
    · exact .imp_distrib
  | @transpose _ p₁ p₂ =>
    rcases formula_of_homLimit p₁ with ⟨i₁, q₁, h₁⟩
    rcases formula_of_homLimit p₂ with ⟨i₂, q₂, h₂⟩
    rcases directed_of (· ≤ ·) i₁ i₂ with ⟨i, h₃, h₄⟩
    let q₁' := (φ.hom i₁ i h₃).onFormula q₁
    let q₂' := (φ.hom i₂ i h₄).onFormula q₂
    exists i, (~ q₁' ⇒ ~ q₂') ⇒ q₂' ⇒ q₁'
    constructor
    · simp [Hom.onFormula, Hom.onFormula_neg, q₁', q₂']; simp_rw [←Hom.comp_onFormula, homLimit_comp_hom]; simp [h₁, h₂]
    · exact .transpose
  | @forall_elim _ p t =>
    rcases term_of_homLimit t with ⟨i₁, t', h₁⟩
    rcases formula_of_homLimit p with ⟨i₂, q, h₂⟩
    rcases directed_of (· ≤ ·) i₁ i₂ with ⟨i, h₃, h₄⟩
    let t'' := (φ.hom i₁ i h₃).onTerm t'
    let q' := (φ.hom i₂ i h₄).onFormula q
    exists i, ∀' q' ⇒ q'[↦ₛ t'']ₚ
    constructor
    · simp [Hom.onFormula, Hom.onFormula_subst_single, t'', q']
      simp_rw [←Hom.comp_onFormula, ←Hom.comp_onTerm, homLimit_comp_hom]
      simp [h₁, h₂]
    · exact .forall_elim
  | @forall_self _ p =>
    rcases formula_of_homLimit p with ⟨i, q, h₂⟩
    exists i, q ⇒ ∀' (↑ₚq)
    constructor
    · simp [Hom.onFormula, Hom.onFormula_shift, h₂]
    · exact .forall_self
  | @forall_imp _ p₁ p₂ =>
    rcases formula_of_homLimit p₁ with ⟨i₁, q₁, h₁⟩
    rcases formula_of_homLimit p₂ with ⟨i₂, q₂, h₂⟩
    rcases directed_of (· ≤ ·) i₁ i₂ with ⟨i, h₃, h₄⟩
    let q₁' := (φ.hom i₁ i h₃).onFormula q₁
    let q₂' := (φ.hom i₂ i h₄).onFormula q₂
    exists i, ∀' (q₁' ⇒ q₂') ⇒ ∀' q₁' ⇒ ∀' q₂'
    constructor
    · simp [Hom.onFormula, q₁', q₂']; simp_rw [←Hom.comp_onFormula, homLimit_comp_hom]; simp [h₁, h₂]
    · exact .forall_imp
  | @eq_refl _ t =>
    rcases term_of_homLimit t with ⟨i, t', h₁⟩
    exists i, t' ≐ t'
    constructor
    · simp [Hom.onFormula, h₁]
    · exact .eq_refl
  | @eq_symm _ t₁ t₂ =>
    rcases term_of_homLimit t₁ with ⟨i₁, t₁', h₁⟩
    rcases term_of_homLimit t₂ with ⟨i₂, t₂', h₂⟩
    rcases directed_of (· ≤ ·) i₁ i₂ with ⟨i, h₃, h₄⟩
    let t₁'' := (φ.hom i₁ i h₃).onTerm t₁'
    let t₂'' := (φ.hom i₂ i h₄).onTerm t₂'
    exists i, t₁'' ≐ t₂'' ⇒ t₂'' ≐ t₁''
    constructor
    · simp [Hom.onFormula, t₁'', t₂'']
      simp_rw [←Hom.comp_onTerm, homLimit_comp_hom]
      simp [h₁, h₂]
    · exact .eq_symm
  | @eq_trans _ t₁ t₂ t₃ =>
    rcases term_of_homLimit t₁ with ⟨i₁, t₁', h₁⟩
    rcases term_of_homLimit t₂ with ⟨i₂, t₂', h₂⟩
    rcases term_of_homLimit t₃ with ⟨i₃, t₃', h₃⟩
    rcases directed_of_three (α := ι) (· ≤ ·) i₁ i₂ i₃ with ⟨i, h₄, h₅, h₆⟩
    let t₁'' := (φ.hom i₁ i h₄).onTerm t₁'
    let t₂'' := (φ.hom i₂ i h₅).onTerm t₂'
    let t₃'' := (φ.hom i₃ i h₆).onTerm t₃'
    exists i, t₁'' ≐ t₂'' ⇒ t₂'' ≐ t₃'' ⇒ t₁'' ≐ t₃''
    constructor
    · simp [Hom.onFormula, t₁'', t₂'', t₃'']
      simp_rw [←Hom.comp_onTerm, homLimit_comp_hom]
      simp [h₁, h₂, h₃]
    · exact .eq_trans
  | @eq_congr_func _ _ v₁ v₂ f =>
    choose u₁ w₁ h₁ using λ i => term_of_homLimit (v₁ i)
    rcases directed_of_vec (α := ι) (· ≤ ·) u₁ with ⟨i₁, h₁'⟩
    choose u₂ w₂ h₂ using λ i => term_of_homLimit (v₂ i)
    rcases directed_of_vec (α := ι) (· ≤ ·) u₂ with ⟨i₂, h₂'⟩
    rcases f with ⟨i₃, f⟩
    rcases directed_of_three (α := ι) (· ≤ ·) i₁ i₂ i₃ with ⟨i, h₃, h₄, h₅⟩
    let v₁' := λ x => (φ.hom (u₁ x) i ((h₁' x).trans h₃)).onTerm (w₁ x)
    let v₂' := λ x => (φ.hom (u₂ x) i ((h₂' x).trans h₄)).onTerm (w₂ x)
    let f' := (φ.hom i₃ i h₅).onFunc f
    exists i, (⋀ i, v₁' i ≐ v₂' i) ⇒ f' ⬝ᶠ v₁' ≐ f' ⬝ᶠ v₂'
    constructor
    · simp [Hom.onFormula, Hom.onTerm, Hom.onFormula_andN, v₁', v₂', f']
      simp_rw [←Hom.comp_onTerm, homLimit_comp_hom]
      simp [←h₁, ←h₂]
      apply Quotient.sound
      exists i, h₅, le_refl i
      rw [←Hom.comp_onFunc, φ.hom_comp]
    · exact .eq_congr_func
  | @eq_congr_rel _ _ v₁ v₂ r =>
    choose u₁ w₁ h₁ using λ i => term_of_homLimit (v₁ i)
    rcases directed_of_vec (α := ι) (· ≤ ·) u₁ with ⟨i₁, h₁'⟩
    choose u₂ w₂ h₂ using λ i => term_of_homLimit (v₂ i)
    rcases directed_of_vec (α := ι) (· ≤ ·) u₂ with ⟨i₂, h₂'⟩
    rcases r with ⟨i₃, r⟩
    rcases directed_of_three (α := ι) (· ≤ ·) i₁ i₂ i₃ with ⟨i, h₃, h₄, h₅⟩
    let v₁' := λ x => (φ.hom (u₁ x) i ((h₁' x).trans h₃)).onTerm (w₁ x)
    let v₂' := λ x => (φ.hom (u₂ x) i ((h₂' x).trans h₄)).onTerm (w₂ x)
    let r' := (φ.hom i₃ i h₅).onRel r
    exists i, (⋀ i, v₁' i ≐ v₂' i) ⇒ r' ⬝ʳ v₁' ⇒ r' ⬝ʳ v₂'
    constructor
    · simp [Hom.onFormula, Hom.onTerm, Hom.onFormula_andN, v₁', v₂', r']
      simp_rw [←Hom.comp_onTerm, homLimit_comp_hom]
      simp [←h₁, ←h₂]
      apply Quotient.sound
      exists i, h₅, le_refl i
      rw [←Hom.comp_onRel, φ.hom_comp]
    · exact .eq_congr_rel
  | @all _ p _ ih =>
    rcases ih with ⟨i, q, h₁, h₂⟩
    exists i, ∀' q
    constructor
    · simp [Hom.onFormula, h₁]
    · exact .all h₂

theorem proof_of_homLimit [Nonempty ι] (h : Γ ⊢ p) :
  ∃ i Δ q, (φ.homLimit i).onFormula '' Δ ⊆ Γ ∧ p = (φ.homLimit i).onFormula q ∧ Δ.Finite ∧ Δ ⊢ q := by
  induction h with
  | @hyp p h =>
    rcases formula_of_homLimit p with ⟨i, q, h₁⟩
    exists i, {q}, q, by simp [←h₁, h], h₁, by simp
    exact .hyp (Set.mem_singleton q)
  | ax h =>
    rcases axiom_of_homLimit h with ⟨i, p, h₁, h₂⟩
    exists i, ∅, p, by simp, h₁, by simp
    exact .ax h₂
  | mp _ _ ih₁ ih₂ =>
    rcases ih₁ with ⟨i₁, Δ₁, p, h₁, h₂, h₃, h₃'⟩
    cases' p with _ _ _ _ _ _ _ _ _ p q <;> simp [Hom.onFormula] at h₂
    rcases ih₂ with ⟨i₂, Δ₂, r, h₄, h₅, h₆, h₆'⟩
    rcases formula_hom_eq_of_homLimit_eq _ _ (h₂.left.symm.trans h₅) with ⟨i, h, h', h''⟩
    exists i, (φ.hom i₁ i h).onFormula '' Δ₁ ∪ (φ.hom i₂ i h').onFormula '' Δ₂, (φ.hom i₁ i h).onFormula q
    constructor
    · simp_rw [Set.image_union, Set.union_subset_iff, Set.image_image, ←Hom.comp_onFormula, homLimit_comp_hom]
      exact ⟨h₁, h₄⟩
    constructor
    · rw [←Hom.comp_onFormula, homLimit_comp_hom, h₂.right]
    constructor
    · simp; constructor <;> apply Set.Finite.image <;> assumption
    · apply Proof.mp (.weaken Set.subset_union_left (Hom.on_proof h₃'))
      apply Proof.weaken Set.subset_union_right
      rw [h'']
      exact Hom.on_proof h₆'

theorem subset_of_monotone_union [Nonempty ι] {Γ : (i : ι) → (L i).FormulaSet n} {Δ : (L i).FormulaSet n}
  (h₁ : ∀ i j h, (φ.hom i j h).onFormula '' Γ i ⊆ Γ j)
  (h₂ : (φ.homLimit i).onFormula '' Δ ⊆ ⋃i, (φ.homLimit i).onFormula '' Γ i)
  (h : Δ.Finite) :
  ∃ j h, (φ.hom i j h).onFormula '' Δ ⊆ Γ j := by
  -- simp at h₂; rcases h₂ with ⟨
  induction Δ, h using Set.Finite.induction_on_subset with
  | empty => exists i, le_refl i; simp
  | @insert p Δ' h₃ _ _ h₄ =>
    simp only [Set.image_insert_eq, Set.insert_subset_iff, Set.mem_iUnion] at h₂
    rcases h₂ with ⟨⟨j₂, q, h₆, h₇⟩, h₂'⟩
    apply h₄ at h₂'
    rcases h₂' with ⟨j₁, h₄, h₅⟩
    apply formula_hom_eq_of_homLimit_eq at h₇
    rcases h₇ with ⟨j₃, h₇, h₇', h₇''⟩
    rcases directed_of (· ≤ ·) j₁ j₃ with ⟨k, h₈, h₈'⟩
    exists k, h₄.trans h₈
    rw [Set.image_insert_eq, Set.insert_subset_iff]
    constructor
    · rw [←φ.hom_comp h₇' h₈', Hom.comp_onFormula, ←h₇'', ←Hom.comp_onFormula, φ.hom_comp _ _ (h₇.trans h₈')]
      apply Set.mem_of_subset_of_mem (h₁ j₂ k (h₇.trans h₈'))
      simp; exists q
    · simp_rw [←φ.hom_comp h₄ h₈, Hom.comp_onFormula]
      rw [←Function.comp_def, Set.image_comp]
      apply Set.Subset.trans (Set.image_subset _ h₅)
      apply h₁

def ofChain (L : ℕ → Language) (φ : ∀ i, L i →ᴸ L (i + 1)) : DirectedSystem L where
  hom i j h := Nat.leRecOn h (φ _ ∘ᴸ ·) .id
  hom_id := by simp [Nat.leRecOn_self]
  hom_comp {i j k} h₁ h₂ h₃ := by
    induction k, h₂ using Nat.le_induction with
    | base => simp [Nat.leRecOn_self]; ext <;> simp
    | succ k h₂ ih =>
      simp; rw [Nat.leRecOn_succ (h1 := h₂), Nat.leRecOn_succ (h1 := le_trans h₁ h₂)];
      have := ih (le_trans h₁ h₂)
      simp at this
      rw [Hom.comp_assoc, this]

theorem ofChain_hom_succ {L : ℕ → Language} {φ : ∀ i, L i →ᴸ L (i + 1)} :
  (ofChain L φ).hom i i.succ h = φ i := by simp [ofChain, Nat.leRecOn_succ', Hom.comp_id]

theorem monotone_chain {L : ℕ → Language} {φ : ∀ i, L i →ᴸ L (i + 1)} {Γ : (i : ℕ) → (L i).FormulaSet n}
  (h₁ : ∀ i, (φ i).onFormula '' Γ i ⊆ Γ (i + 1)) :
  ∀ i j h, ((ofChain L φ).hom i j h).onFormula '' Γ i ⊆ Γ j := by
  intro i j h
  induction h with
  | refl => simp_rw [hom_id]; simp [Hom.id_onFormula]
  | @step j h ih =>
    simp at h
    apply Set.Subset.trans _ (h₁ j)
    simp_rw [←hom_comp _ h (Nat.le_succ j), Hom.comp_onFormula]
    rw [←Function.comp_def, Set.image_comp]
    simp only [ofChain_hom_succ]
    apply Set.image_subset
    exact ih

end FirstOrder.Language.DirectedSystem
