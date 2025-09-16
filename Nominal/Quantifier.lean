import Mathlib.Order.Filter.Cofinite
import Nominal.Instances
import Nominal.Rel

open Filter Finperm

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
    (hp : FinitelySupported 𝔸 p) :
    (ν a, p a) ∨ (ν a, ¬p a) := by
  obtain h | h := hp.finite_or_finite
  · right
    apply h.subset
    simp only [Set.compl_setOf, not_not, subset_rfl]
  · left
    exact h

theorem NewNames.of_not [DecidableEq 𝔸] [Infinite 𝔸] (p : 𝔸 → Prop)
    (hp : FinitelySupported 𝔸 p) :
    (¬ν a, p a) → ν a, ¬p a := by
  have := newNames_em p hp
  tauto

theorem newNames_not [DecidableEq 𝔸] [Infinite 𝔸] (p : 𝔸 → Prop)
    (hp : FinitelySupported 𝔸 p) :
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

theorem newNames_or_left [DecidableEq 𝔸] [Infinite 𝔸] (p q : 𝔸 → Prop)
    (hp : FinitelySupported 𝔸 p) :
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

theorem newNames_or_right [DecidableEq 𝔸] [Infinite 𝔸] (p q : 𝔸 → Prop)
    (hq : FinitelySupported 𝔸 q) :
    (ν a, p a ∨ q a) ↔ (ν a, p a) ∨ (ν a, q a) := by
  have := newNames_or_left q p hq
  simp only [or_comm (a := q _), or_comm (a := ν a, q a)] at this
  exact this

theorem newNames_imp_left [DecidableEq 𝔸] [Infinite 𝔸] (p q : 𝔸 → Prop)
    (hp : FinitelySupported 𝔸 p) :
    (ν a, p a → q a) ↔ (ν a, p a) → (ν a, q a) := by
  simp only [imp_iff_not_or]
  rw [newNames_or_left _ _ hp.not, newNames_not p hp]

theorem newNames_iff [DecidableEq 𝔸] [Infinite 𝔸] (p q : 𝔸 → Prop)
    (hp : FinitelySupported 𝔸 p) (hq : FinitelySupported 𝔸 q) :
    (ν a, p a ↔ q a) ↔ ((ν a, p a) ↔ (ν a, q a)) := by
  conv => lhs; simp only [iff_iff_implies_and_implies]
  rw [newNames_and, newNames_imp_left p q hp, newNames_imp_left q p hq]
  tauto

theorem NewNames.perm [DecidableEq 𝔸] {p : 𝔸 → Prop} (h : ν a, p a) (π : Finperm 𝔸) :
    ν a, p (π a) := by
  rw [newNames_def'] at h ⊢
  apply (h.image (π⁻¹ ·)).subset
  intro a ha
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_setOf_eq]
  exact ⟨_, ha, Finperm.inv_apply_self π a⟩

theorem NewNames.of_perm [DecidableEq 𝔸] {p : 𝔸 → Prop} {π : Finperm 𝔸} (h : ν a, p (π a)) :
    ν a, p a := by
  have := h.perm π⁻¹
  simp only [Finperm.apply_inv_self] at this
  exact this

theorem newNames_perm [DecidableEq 𝔸] {p : 𝔸 → Prop} (π : Finperm 𝔸) :
    (ν a, p a) ↔ (ν a, p (π a)) :=
  ⟨λ h ↦ h.perm π, λ h ↦ h.of_perm⟩

theorem newNames_notMem [DecidableEq 𝔸] (s : Finset 𝔸) :
    ν a, a ∉ s := by
  simp only [newNames_def', Set.compl_setOf, Decidable.not_not, Finset.setOf_mem,
    Finset.finite_toSet]

theorem newNames_fresh [DecidableEq 𝔸] [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (x : α) :
    ν a : 𝔸, a #[𝔸] x := by
  simp only [name_fresh_iff, newNames_def', Set.compl_setOf, Decidable.not_not, Finset.setOf_mem,
    Finset.finite_toSet]

theorem FinitelySupported.new [DecidableEq 𝔸] {α β : Type*}
    [MulPerm 𝔸 α] [MulPerm 𝔸 β] {f : α → β} (hf : FinitelySupported 𝔸 f) :
    ν (a : 𝔸), ν (b : 𝔸), ∀ x, swap a b ⬝ f x = f (swap a b ⬝ x) := by
  rw [Function.finitelySupported_iff] at hf
  obtain ⟨s, hs⟩ := hf
  have := newNames_notMem s
  apply this.mono
  intro a ha
  apply this.mono
  intro b hb x
  rw [hs]
  intro c hc
  rw [swap_apply_of_ne_of_ne]
  · rintro rfl
    contradiction
  · rintro rfl
    contradiction

theorem finitelySupported_iff [DecidableEq 𝔸] [Infinite 𝔸] {α : Sort*} [MulPerm 𝔸 α] (x : α) :
    FinitelySupported 𝔸 x ↔ ν (a : 𝔸) (b : 𝔸), swap a b ⬝ x = x := by
  constructor
  · rintro ⟨s, hs⟩
    rw [supports_iff'] at hs
    apply (newNames_notMem s).mono
    intro a ha
    apply (newNames_notMem s).mono
    intro b hb
    exact hs a b ha hb
  · intro h
    simp only [FinitelySupported, supports_iff, ne_eq]
    rw [newNames_def'] at h
    use h.toFinset
    intro a b ha hb hab
    simp only [Set.Finite.mem_toFinset, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha hb
    obtain ⟨c, hac, hbc, hcb⟩ := (ha.and (hb.and (newNames_notMem {b}))).exists
    simp only [Finset.mem_singleton] at hcb
    rw [swap_triple a b c hab (Ne.symm hcb), mul_perm, mul_perm, hac, hbc, hac]

/-!
## The some/any theorem
-/

variable [DecidableEq 𝔸] [Infinite 𝔸] {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β]

theorem exists_of_newNames (p : 𝔸 → α → Prop) (x : α) :
    (ν a, p a x) → ∃ a #[𝔸] x, p a x := by
  intro h
  apply NewNames.exists
  simp only [newNames_and, newNames_fresh, h, and_self]

theorem newNames_of_exists (p : 𝔸 → α → Prop) (hp : Equivariant 𝔸 p) (x : α) :
    (∃ a #[𝔸] x, p a x) → ν a, p a x := by
  rintro ⟨a, h₁, h₂⟩
  apply (supp 𝔸 x).finite_toSet.subset
  intro b hb
  contrapose hb
  simp only [Finset.mem_coe, ← name_fresh_iff] at hb
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  rwa [hp.rename_of_fresh b a x hb h₁]

theorem forall_fresh_of_newNames (p : 𝔸 → α → Prop) (hp : Equivariant 𝔸 p) (x : α) :
    (ν a, p a x) → ∀ a #[𝔸] x, p a x := by
  intro h
  by_contra! h'
  have := newNames_of_exists (λ a x ↦ ¬p a x) hp.not₂ x h'
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

theorem newNames_iff_exists (p : 𝔸 → α → Prop) (hp : Equivariant 𝔸 p) (x : α) :
    (ν a, p a x) ↔ ∃ a #[𝔸] x, p a x :=
  ⟨exists_of_newNames p x, newNames_of_exists p hp x⟩

theorem newNames_iff_forall (p : 𝔸 → α → Prop) (hp : Equivariant 𝔸 p) (x : α) :
    (ν a, p a x) ↔ ∀ a #[𝔸] x, p a x :=
  ⟨forall_fresh_of_newNames p hp x, newNames_of_forall_fresh p x⟩

theorem Equivariant.exists_iff_forall (p : 𝔸 → α → Prop) (hp : Equivariant 𝔸 p) (x : α) :
    (∃ a #[𝔸] x, p a x) ↔ (∀ a #[𝔸] x, p a x) := by
  rw [← newNames_iff_exists p hp, newNames_iff_forall p hp]

theorem newNames_iff_exists₂ (p : 𝔸 → α → β → Prop) (hp : Equivariant 𝔸 p) (x : α) (y : β) :
    (ν a, p a x y) ↔ ∃ a #[𝔸] x, a #[𝔸] y ∧ p a x y := by
  rw [newNames_iff_exists _ hp.uncurry₂ ⟨x, y⟩]
  simp only [Prod.fresh_iff, and_assoc]

theorem newNames_iff_forall₂ (p : 𝔸 → α → β → Prop) (hp : Equivariant 𝔸 p) (x : α) (y : β) :
    (ν a, p a x y) ↔ ∀ a #[𝔸] x, a #[𝔸] y → p a x y := by
  rw [newNames_iff_forall _ hp.uncurry₂ ⟨x, y⟩]
  simp only [Prod.fresh_iff, and_imp]

omit [Infinite 𝔸] in
theorem app_equivariant : Equivariant 𝔸 (λ a (p : FS 𝔸 (𝔸 → α → Prop)) x ↦ p.val a x) := by
  intro π
  ext p y
  simp only [Function.perm_def, perm_name_eq, FS.perm_coe, inv_inv, apply_inv_self,
    IsDiscrete.perm_eq, perm_inv_perm]

theorem newNames_iff_exists_fresh (p : 𝔸 → α → Prop) (hp : FinitelySupported 𝔸 p) (x : α) :
    (ν a, p a x) ↔ ∃ a #[𝔸] p, a #[𝔸] x ∧ p a x := by
  have := newNames_iff_exists₂ (𝔸 := 𝔸) (α := FS 𝔸 (𝔸 → α → Prop)) (β := α)
    (λ a p x ↦ p.val a x) app_equivariant ⟨p, hp⟩ x
  simp only [FS.fresh_iff] at this
  exact this

theorem newNames_iff_forall_fresh (p : 𝔸 → α → Prop) (hp : FinitelySupported 𝔸 p) (x : α) :
    (ν a, p a x) ↔ ∀ a #[𝔸] p, a #[𝔸] x → p a x := by
  have := newNames_iff_forall₂ (𝔸 := 𝔸) (α := FS 𝔸 (𝔸 → α → Prop)) (β := α)
    (λ a p x ↦ p.val a x) app_equivariant ⟨p, hp⟩ x
  simp only [FS.fresh_iff] at this
  exact this

/-!
## The freshness theorem
-/

theorem fresh_of_coinjective {r : α → β → Prop} (h₁ : Rel.Coinjective r)
    (h₂ : FinitelySupported 𝔸 r)
    {x : α} {y : β} (h : r x y) {a : 𝔸} (hr : a #[𝔸] r) (hx : a #[𝔸] x) : a #[𝔸] y := by
  have := supp_supports' r h₂
  simp only [Function.supports_iff, funext_iff, Function.perm_def, IsDiscrete.perm_eq,
    eq_iff_iff] at this
  rw [fresh_iff_exists_swap_perm_eq]
  obtain ⟨b, hbx, hby, hbr⟩ := ((newNames_fresh (𝔸 := 𝔸) x).and
    ((newNames_fresh y).and (newNames_notMem (supp 𝔸 r)))).exists
  refine ⟨b, hby, ?_⟩
  have := this (swap a b) ?_ x y
  · rw [swap_perm_eq_of_fresh a b x hx hbx, swap_inv] at this
    have := h₁.coinjective h (this.mpr h)
    rw [← this]
  · intro c hc
    rw [swap_apply_of_ne_of_ne]
    · rintro rfl
      rw [name_fresh_iff] at hr
      contradiction
    · rintro rfl
      contradiction

/-- The `fresh` relation from the freshness theorem. -/
def freshRel (r : FS 𝔸 (𝔸 → α → Prop)) (x : α) : Prop :=
  Rel.Coinjective r.val ∧ ν a, r.val a x

theorem freshRel_coinjective : Rel.Coinjective (freshRel (𝔸 := 𝔸) (α := α)) := by
  constructor
  rintro x y r ⟨hr, hrx⟩ ⟨-, hry⟩
  obtain ⟨a, hax, hay⟩ := (hrx.and hry).exists
  exact hr.coinjective hax hay

theorem mem_freshRel_dom (r : FS 𝔸 (𝔸 → α → Prop))
    (h : Rel.Coinjective r.val) (h' : ν a, ∃ x, a #[𝔸] x ∧ r.val a x) :
    r ∈ Rel.dom freshRel := by
  obtain ⟨a, ⟨x, hax, hrax⟩, har⟩ := (h'.and (newNames_fresh r)).exists
  refine ⟨x, h, ?_⟩
  rw [newNames_iff_exists_fresh _ r.prop]
  rw [FS.fresh_iff] at har
  exact ⟨a, har, hax, hrax⟩

/-- **The freshness theorem** for relations. -/
theorem exists_of_newNames_fresh (r : 𝔸 → α → Prop)
    (h₁ : Rel.Coinjective r) (h₂ : FinitelySupported 𝔸 r)
    (h₃ : ν a, ∃ x, a #[𝔸] x ∧ r a x) :
    ∃! x, ν a, r a x := by
  obtain ⟨x, hx⟩ := mem_freshRel_dom ⟨r, h₂⟩ h₁ h₃
  refine ⟨x, hx.2, ?_⟩
  intro y hy
  obtain ⟨a, hax, hay⟩ := (hx.2.and hy).exists
  exact h₁.coinjective hay hax

noncomputable def freshName {α : Sort*} [Nonempty α] (f : 𝔸 → α) : α :=
  Classical.epsilon (λ x ↦ ν a, f a = x)

/-- The `fresh` syntax for creating terms that need, but do not depend on, a choice of name. -/
notation3 "fresh "(...)", "r:(scoped p => freshName p) => r

/-- **The freshness theorem** for functions. -/
theorem fresh_spec [Nonempty α] (f : 𝔸 → α) (hf₁ : ν a, a #[𝔸] f a) (hf₂ : FinitelySupported 𝔸 f) :
    ν a, (fresh b, f b) = f a := by
  have := exists_of_newNames_fresh _ ?_ hf₂.graph ?_
  · obtain ⟨x, hx, -⟩ := this
    rw [freshName]
    have := Classical.epsilon_spec (p := λ x ↦ ν a, f a = x) ⟨x, hx⟩
    apply (hx.and this).mono
    rintro a ⟨ha₁, ha₂⟩
    exact ha₂.symm
  · constructor
    rintro x y a rfl rfl
    rfl
  · apply hf₁.mono
    simp only [exists_eq_right', imp_self, implies_true]
