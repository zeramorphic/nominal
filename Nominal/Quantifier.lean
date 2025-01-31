import Mathlib.Order.Filter.Cofinite
import Nominal.Fresh

open Filter
open scoped Pointwise

variable {𝔸 : Type*}

def NewNames (p : 𝔸 → Prop) : Prop :=
  ∀ᶠ a in cofinite, p a

notation3 "ν "(...)", "r:(scoped p => NewNames p) => r

theorem newNames_def (p : 𝔸 → Prop) :
    (ν a, p a) ↔ ∀ᶠ a in cofinite, p a :=
  Iff.rfl

theorem newNames_def' (p : 𝔸 → Prop) :
    (ν a, p a) ↔ {a | p a}ᶜ.Finite :=
  Iff.rfl

theorem NewNames.exists [Infinite 𝔸] {p : 𝔸 → Prop} (h : ν a, p a) :
    ∃ a, p a :=
  Eventually.exists h

@[simp]
theorem newNames_true :
    ν _ : 𝔸, True :=
  eventually_true _

theorem newNames_of_forall {p : 𝔸 → Prop} :
    (∀ a, p a) → ν a, p a :=
  Eventually.of_forall

@[simp]
theorem not_newNames_false [Infinite 𝔸] :
    ¬ν _ : 𝔸, False :=
  eventually_false_iff_eq_bot.mp.mt NeBot.ne'

@[simp]
theorem newNames_const [Infinite 𝔸] {p : Prop} :
    (ν _ : 𝔸, p) ↔ p :=
  eventually_const

theorem newNames_mp {p q : 𝔸 → Prop} (hp : ν a, p a) (hq : ν a, p a → q a) :
    ν a, q a :=
  Eventually.mp hp hq

theorem newNames_mono {p q : 𝔸 → Prop} (hp : ν a, p a) (hq : ∀ a, p a → q a) :
    ν a, q a :=
  Eventually.mono hp hq

theorem NewNames.mono {p q : 𝔸 → Prop} (h : ν a, p a) (h' : ∀ a, p a → q a) :
    ν a, q a :=
  Eventually.mono h h'

theorem forall_newNames_of_newNames_forall {α : Type*} {p : 𝔸 → α → Prop}
    (h : ν a, ∀ x, p a x) : ∀ x, ν a, p a x :=
  forall_eventually_of_eventually_forall h

@[simp]
theorem newNames_and {p q : 𝔸 → Prop} :
    (ν a, p a ∧ q a) ↔ (ν a, p a) ∧ (ν a, q a) :=
  eventually_and

theorem NewNames.and {p q : 𝔸 → Prop} (h : ν a, p a) (h' : ν a, q a) :
    ν a, p a ∧ q a :=
  Eventually.and h h'

theorem NewNames.congr {p q : 𝔸 → Prop} (h : ν a, p a ↔ q a) :
    (ν a, p a) ↔ (ν a, q a) :=
  eventually_congr h

@[simp]
theorem newNames_all {ι : Sort*} [Finite ι] {p : ι → 𝔸 → Prop} :
    (ν a, ∀ i, p i a) ↔ ∀ i, ν a, p i a :=
  eventually_all

@[simp]
theorem newNames_all_finite {ι : Type*} {I : Set ι} (hI : I.Finite) {p : ι → 𝔸 → Prop} :
    (ν a, ∀ i ∈ I, p i a) ↔ ∀ i ∈ I, ν a, p i a :=
  eventually_all_finite hI

@[simp]
theorem newNames_all_finset {ι : Type*} (I : Finset ι) {p : ι → 𝔸 → Prop} :
    (ν a, ∀ i ∈ I, p i a) ↔ ∀ i ∈ I, ν a, p i a :=
  eventually_all_finset I

@[simp]
theorem newNames_or_distrib_left {p : Prop} {q : 𝔸 → Prop} :
    (ν a, p ∨ q a) ↔ p ∨ ν a, q a :=
  eventually_or_distrib_left

@[simp]
theorem newNames_or_distrib_right {p : 𝔸 → Prop} {q : Prop} :
    (ν a, p a ∨ q) ↔ (ν a, p a) ∨ q :=
  eventually_or_distrib_right

@[simp]
theorem newNames_imp_distrib_left {p : Prop} {q : 𝔸 → Prop} :
    (ν a, p → q a) ↔ p → ν a, q a :=
  eventually_imp_distrib_left

theorem NewNames.not [Infinite 𝔸] {p : 𝔸 → Prop} :
    (ν a, ¬p a) → ¬ν a, p a := by
  intro h₁ h₂
  have := h₁.and h₂
  simp only [not_and_self, not_newNames_false] at this

/-- The law of the excluded middle for finitely supported predicates. -/
theorem newNames_em [DecidableEq 𝔸] [Infinite 𝔸] (p : 𝔸 → Prop)
    (hp : FinitelySupportedPred 𝔸 p) :
    (ν a, p a) ∨ (ν a, ¬p a) := by
  obtain h | h := hp.finite_or_finite
  · right
    apply h.subset
    simp only [Set.compl_setOf, not_not, subset_rfl]
  · left
    exact h

theorem NewNames.of_not [DecidableEq 𝔸] [Infinite 𝔸] (p : 𝔸 → Prop)
    (hp : FinitelySupportedPred 𝔸 p) :
    (¬ν a, p a) → ν a, ¬p a := by
  have := newNames_em p hp
  tauto

theorem newNames_not [DecidableEq 𝔸] [Infinite 𝔸] (p : 𝔸 → Prop)
    (hp : FinitelySupportedPred 𝔸 p) :
    (ν a, ¬p a) ↔ (¬ν a, p a) :=
  ⟨NewNames.not, NewNames.of_not p hp⟩

theorem NewNames.or_left {p : 𝔸 → Prop} (h : ν a, p a) (q : 𝔸 → Prop) :
    ν a, p a ∨ q a := by
  apply h.mono
  exact λ _ ↦ Or.inl

theorem NewNames.or_right {p : 𝔸 → Prop} (h : ν a, p a) (q : 𝔸 → Prop) :
    ν a, q a ∨ p a := by
  apply h.mono
  exact λ _ ↦ Or.inr

theorem newNames_or_left [DecidableEq 𝔸] [Infinite 𝔸] (p q : 𝔸 → Prop) (hp : FinitelySupportedPred 𝔸 p) :
    (ν a, p a ∨ q a) ↔ (ν a, p a) ∨ (ν a, q a) := by
  constructor
  · intro h
    obtain h' | h' := newNames_em p hp
    · left
      exact h'
    · right
      apply (h.and h').mono
      tauto
  · rintro (h | h)
    · exact h.or_left q
    · exact h.or_right p

theorem newNames_or_right [DecidableEq 𝔸] [Infinite 𝔸] (p q : 𝔸 → Prop) (hq : FinitelySupportedPred 𝔸 q) :
    (ν a, p a ∨ q a) ↔ (ν a, p a) ∨ (ν a, q a) := by
  have := newNames_or_left q p hq
  simp only [or_comm (a := q _), or_comm (a := ν a, q a)] at this
  exact this

theorem newNames_imp_left [DecidableEq 𝔸] [Infinite 𝔸] (p q : 𝔸 → Prop) (hp : FinitelySupportedPred 𝔸 p) :
    (ν a, p a → q a) ↔ (ν a, p a) → (ν a, q a) := by
  simp only [imp_iff_not_or]
  rw [newNames_or_left _ _ hp.not, newNames_not p hp]

theorem newNames_iff [DecidableEq 𝔸] [Infinite 𝔸] (p q : 𝔸 → Prop)
    (hp : FinitelySupportedPred 𝔸 p) (hq : FinitelySupportedPred 𝔸 q) :
    (ν a, p a ↔ q a) ↔ ((ν a, p a) ↔ (ν a, q a)) := by
  conv => lhs; simp only [iff_iff_implies_and_implies]
  rw [newNames_and, newNames_imp_left p q hp, newNames_imp_left q p hq]
  tauto

theorem NewNames.smul [DecidableEq 𝔸] {p : 𝔸 → Prop} (h : ν a, p a) (π : Finperm 𝔸) :
    ν a, p (π a) := by
  rw [newNames_def'] at h ⊢
  apply (h.image (π⁻¹ ·)).subset
  intro a ha
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_setOf_eq]
  exact ⟨_, ha, Finperm.inv_apply_self π a⟩

theorem NewNames.of_smul [DecidableEq 𝔸] {p : 𝔸 → Prop} {π : Finperm 𝔸} (h : ν a, p (π a)) :
    ν a, p a := by
  have := h.smul π⁻¹
  simp only [Finperm.apply_inv_self] at this
  exact this

theorem newNames_smul [DecidableEq 𝔸] {p : 𝔸 → Prop} (π : Finperm 𝔸) :
    (ν a, p a) ↔ (ν a, p (π a)) :=
  ⟨λ h ↦ h.smul π, λ h ↦ h.of_smul⟩

theorem newNames_not_mem [DecidableEq 𝔸] (s : Finset 𝔸) :
    ν a, a ∉ s := by
  simp only [newNames_def', Set.compl_setOf, Decidable.not_not, Finset.setOf_mem,
    Finset.finite_toSet]

theorem newNames_fresh [DecidableEq 𝔸] [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (x : α) :
    ν a : 𝔸, a #[𝔸] x := by
  simp only [name_fresh_iff, newNames_def', Set.compl_setOf, Decidable.not_not, Finset.setOf_mem,
    Finset.finite_toSet]

variable [DecidableEq 𝔸] [Infinite 𝔸] {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β]

theorem exists_of_newNames (p : 𝔸 → α → Prop) (x : α) :
    (ν a, p a x) → ∃ a #[𝔸] x, p a x := by
  intro h
  apply NewNames.exists
  simp only [newNames_and, newNames_fresh, h, and_self]

theorem newNames_of_exists (p : 𝔸 → α → Prop) (hp : EquivariantRel 𝔸 p) (x : α) :
    (∃ a #[𝔸] x, p a x) → ν a, p a x := by
  rintro ⟨a, h₁, h₂⟩
  apply (supp 𝔸 x).finite_toSet.subset
  intro b hb
  contrapose hb
  simp only [Finset.mem_coe, ← name_fresh_iff] at hb
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  rwa [hp.rename_of_fresh b a x hb h₁]

theorem forall_fresh_of_newNames (p : 𝔸 → α → Prop) (hp : EquivariantRel 𝔸 p) (x : α) :
    (ν a, p a x) → ∀ a #[𝔸] x, p a x := by
  intro h
  by_contra! h'
  have := newNames_of_exists (λ a x ↦ ¬p a x) hp.not x h'
  have := h.and this
  simp only [and_not_self, not_newNames_false] at this

theorem newNames_of_forall_fresh (p : 𝔸 → α → Prop) (x : α) :
    (∀ a #[𝔸] x, p a x) → ν a, p a x := by
  intro h
  apply (supp 𝔸 x).finite_toSet.subset
  intro b hb
  contrapose hb
  simp only [Finset.mem_coe, ← name_fresh_iff] at hb
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  exact h b hb

theorem newNames_iff_exists (p : 𝔸 → α → Prop) (hp : EquivariantRel 𝔸 p) (x : α) :
    (ν a, p a x) ↔ ∃ a #[𝔸] x, p a x :=
  ⟨exists_of_newNames p x, newNames_of_exists p hp x⟩

theorem newNames_iff_forall (p : 𝔸 → α → Prop) (hp : EquivariantRel 𝔸 p) (x : α) :
    (ν a, p a x) ↔ ∀ a #[𝔸] x, p a x :=
  ⟨forall_fresh_of_newNames p hp x, newNames_of_forall_fresh p x⟩

theorem EquivariantRel.exists_iff_forall (p : 𝔸 → α → Prop) (hp : EquivariantRel 𝔸 p) (x : α) :
    (∃ a #[𝔸] x, p a x) ↔ (∀ a #[𝔸] x, p a x) := by
  rw [← newNames_iff_exists p hp, newNames_iff_forall p hp]
