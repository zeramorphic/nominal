import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Data.Set.Finite
import Nominal.Finperm

/-!
We're working from <https://people.cs.nott.ac.uk/pszvc/mgs/MGS2011_nominal_sets.pdf>.
-/

variable {𝔸 : Type*} [DecidableEq 𝔸]

open MulAction Finperm

instance : MulAction (Finperm 𝔸) 𝔸 where
  smul π a := π a
  one_smul := Finperm.one_apply
  mul_smul := Finperm.mul_apply

@[simp]
theorem Finperm.smul_name_eq (π : Finperm 𝔸) (a : 𝔸) :
    π • a = π a :=
  rfl

theorem Finperm.supports_iff' (𝔸 : Type*) [DecidableEq 𝔸] {α : Type*} [MulAction (Finperm 𝔸) α]
    (s : Finset 𝔸) (x : α) :
    Supports (Finperm 𝔸) (s : Set 𝔸) x ↔ ∀ a b, a ∉ s → b ∉ s → swap a b • x = x := by
  constructor
  · intro hs a b ha hb
    apply hs (swap a b)
    intro c hc
    apply swap_apply_of_ne_of_ne <;>
    · rintro rfl
      contradiction
  · intro h π hπ
    induction π using swap_induction_right
    case one => rw [one_smul]
    case swap π a b ha hab ih =>
      rw [mem_support_iff, not_ne_iff] at ha
      rw [mul_smul]
      by_cases ha' : a ∈ s
      · have := hπ ha'
        rw [mul_smul] at this
        change π (swap a b a) = a at this
        rw [swap_apply_left] at this
        have := ha.trans this.symm
        rw [EmbeddingLike.apply_eq_iff_eq] at this
        contradiction
      by_cases hb' : b ∈ s
      · have := hπ hb'
        rw [mul_smul] at this
        change π (swap a b b) = b at this
        rw [swap_apply_right] at this
        have := ha.symm.trans this
        contradiction
      rw [h a b ha' hb']
      apply ih
      intro c hc
      have := hπ hc
      rwa [smul_name_eq, mul_apply, swap_apply_of_ne_of_ne] at this <;>
      · rintro rfl; contradiction

theorem Finperm.supports_iff (𝔸 : Type*) [DecidableEq 𝔸] {α : Type*} [MulAction (Finperm 𝔸) α]
    (s : Finset 𝔸) (x : α) :
    Supports (Finperm 𝔸) (s : Set 𝔸) x ↔ ∀ a b, a ∉ s → b ∉ s → a ≠ b → swap a b • x = x := by
  rw [supports_iff']
  constructor
  · tauto
  · intro h a b ha hb
    by_cases hab : a = b
    · cases hab
      rw [swap_self, one_smul]
    · exact h a b ha hb hab

theorem Finperm.inter_supports [Infinite 𝔸] {α : Type*} [MulAction (Finperm 𝔸) α]
    (s t : Finset 𝔸) (x : α)
    (hs : Supports (Finperm 𝔸) (s : Set 𝔸) x) (ht : Supports (Finperm 𝔸) (t : Set 𝔸) x) :
    Supports (Finperm 𝔸) ((s ∩ t : Finset 𝔸) : Set 𝔸) x := by
  rw [supports_iff'] at hs ht
  rw [supports_iff]
  intro a b ha hb hab
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset (s ∪ t ∪ {a, b})
  simp at hc
  rw [swap_triple a b c hab (by tauto) (by tauto), mul_smul, mul_smul]
  rw [Finset.mem_inter, not_and] at ha hb
  have : swap a c • x = x := by
    by_cases ha' : a ∈ s
    · exact ht a c (ha ha') (by tauto)
    · exact hs a c ha' (by tauto)
  have : swap b c • x = x := by
    by_cases hb' : b ∈ s
    · exact ht b c (hb hb') (by tauto)
    · exact hs b c hb' (by tauto)
  cc

def FinitelySupported (𝔸 : Type*) [DecidableEq 𝔸] {α : Type*} [MulAction (Finperm 𝔸) α]
    (x : α) : Prop :=
  ∃ s : Finset 𝔸, Supports (Finperm 𝔸) (s : Set 𝔸) x

/-- The minimal support of an object, if it exists. -/
noncomputable def supp (𝔸 : Type*) [DecidableEq 𝔸] {α : Type*} [MulAction (Finperm 𝔸) α] (x : α) :
    Finset 𝔸 :=
  open scoped Classical in
  if hx : FinitelySupported 𝔸 x then
    hx.choose.filter (λ a ↦ ∀ s : Finset 𝔸, Supports (Finperm 𝔸) (s : Set 𝔸) x → a ∈ s)
  else
    ∅

theorem supp_eq_of_not_finitelySupported {α : Type*} [MulAction (Finperm 𝔸) α]
    (x : α) (hx : ¬FinitelySupported 𝔸 x) :
    supp 𝔸 x = ∅ := by
  rw [supp, dif_neg hx]

theorem mem_supp_iff' {α : Type*} [MulAction (Finperm 𝔸) α]
    (x : α) (hx : FinitelySupported 𝔸 x) (a : 𝔸) :
    a ∈ supp 𝔸 x ↔ ∀ s : Finset 𝔸, Supports (Finperm 𝔸) (s : Set 𝔸) x → a ∈ s := by
  classical
  rw [supp, dif_pos hx, Finset.mem_filter, and_iff_right_iff_imp]
  intro ha
  exact ha hx.choose hx.choose_spec

theorem supp_supports' [Infinite 𝔸] {α : Type*} [MulAction (Finperm 𝔸) α]
    (x : α) (hx : FinitelySupported 𝔸 x) :
    Supports (Finperm 𝔸) ((supp 𝔸 x) : Set 𝔸) x := by
  intro π hπ
  obtain ⟨s, hs⟩ := hx
  induction s using Finset.strongInduction
  case H s ih =>
    by_cases ht : ∃ t ⊂ s, Supports (Finperm 𝔸) (t : Set 𝔸) x
    · obtain ⟨t, ht₁, ht₂⟩ := ht
      exact ih t ht₁ ht₂
    simp only [not_exists, not_and] at ht
    suffices s = supp 𝔸 x by
      cases this
      exact hs π hπ
    ext a
    rw [mem_supp_iff' x ⟨s, hs⟩]
    constructor; swap; tauto
    intro ha u hu
    by_contra ha'
    refine ht _ ?_ (inter_supports s u x hs hu)
    rw [Finset.ssubset_iff]
    refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_inter, not_and]
      exact λ _ ↦ ha'
    · intro b
      aesop

theorem supp_minimal [Infinite 𝔸] {α : Type*} [MulAction (Finperm 𝔸) α]
    (x : α) (s : Finset 𝔸) (hs : Supports (Finperm 𝔸) (s : Set 𝔸) x) :
    supp 𝔸 x ⊆ s := by
  intro a ha
  rw [mem_supp_iff' x ⟨s, hs⟩] at ha
  exact ha s hs

class Nominal (𝔸 : Type*) [DecidableEq 𝔸] [Infinite 𝔸] (α : Type*)
    extends MulAction (Finperm 𝔸) α where
  supported : ∀ x : α, FinitelySupported 𝔸 x

variable [Infinite 𝔸]

namespace Nominal

instance : Nominal 𝔸 𝔸 where
  supported := λ a ↦ ⟨{a}, λ _ hπ ↦ hπ (Finset.mem_singleton_self a)⟩

theorem mem_supp_iff {α : Type*} [Nominal 𝔸 α]
    (x : α) (a : 𝔸) :
    a ∈ supp 𝔸 x ↔ ∀ s : Finset 𝔸, Supports (Finperm 𝔸) (s : Set 𝔸) x → a ∈ s :=
  mem_supp_iff' x (Nominal.supported x) a

theorem supp_supports {α : Type*} [Nominal 𝔸 α] (x : α) :
    Supports (Finperm 𝔸) ((supp 𝔸 x) : Set 𝔸) x :=
  supp_supports' x (Nominal.supported x)

@[simp]
theorem name_supp_eq (a : 𝔸) :
    supp 𝔸 a = {a} := by
  ext b
  rw [mem_supp_iff]
  constructor
  · intro h
    exact h {a} (λ _ hπ ↦ hπ (Finset.mem_singleton_self a))
  · intro h
    rw [Finset.mem_singleton] at h
    cases h
    intro s hs
    by_contra ha
    obtain ⟨b, hb⟩ := Infinite.exists_not_mem_finset (s ∪ {a})
    rw [Finset.mem_union, Finset.mem_singleton, not_or] at hb
    have := hs (swap a b) ?_
    · rw [smul_name_eq, swap_apply_left] at this
      tauto
    · intro c hc
      apply swap_apply_of_ne_of_ne <;> aesop

end Nominal

instance {G α : Type*} [Group G] [MulAction G α] : SMul G (Finset α) where
  smul g s := s.map ⟨(g • ·), MulAction.injective g⟩

theorem Finset.smul_def {G α : Type*} [Group G] [MulAction G α]
    (g : G) (s : Finset α) :
    g • s = s.map ⟨(g • ·), MulAction.injective g⟩ :=
  rfl

theorem Finset.mem_smul_iff {G α : Type*} [Group G] [MulAction G α]
    (g : G) (x : α) (s : Finset α) :
    x ∈ g • s ↔ g⁻¹ • x ∈ s := by
  rw [Finset.smul_def]
  aesop

instance {α : Type*} [MulAction (Finperm 𝔸) α] : MulAction (Finperm 𝔸) (Finset α) where
  smul π s := s.map ⟨(π • ·), MulAction.injective π⟩
  one_smul _ := by
    ext
    simp [Finset.mem_smul_iff]
  mul_smul _ _ _ := by
    ext
    simp [Finset.mem_smul_iff, mul_smul]

theorem Finset.smul_eq_of_smul_eq {α β : Type*} [Group β] [MulAction β α]
    (s : Finset α) (b : β) (h : ∀ a ∈ s, b • a = a) :
    b • s = s := by
  ext a
  rw [Finset.mem_smul_iff]
  constructor
  · intro ha
    have := h _ ha
    rw [smul_inv_smul] at this
    rwa [← this] at ha
  · intro ha
    have := h _ ha
    rw [smul_eq_iff_eq_inv_smul] at this
    rwa [this] at ha

theorem Finset.finitelySupported {α : Type*} [Nominal 𝔸 α] (s : Finset α) :
    FinitelySupported 𝔸 s := by
  use s.biUnion (supp 𝔸)
  intro π hπ
  apply Finset.smul_eq_of_smul_eq
  intro x hx
  apply Nominal.supp_supports x
  aesop

instance {α : Type*} [Nominal 𝔸 α] : Nominal 𝔸 (Finset α) where
  supported := Finset.finitelySupported

-- TODO: The version in mathlib isn't general enough!
theorem MulAction.Supports.smul' {α : Type*} [MulAction (Finperm 𝔸) α]
    {s : Finset 𝔸} {x : α}
    (h : Supports (Finperm 𝔸) (s : Set 𝔸) x) (π : Finperm 𝔸) :
    Supports (Finperm 𝔸) ((π • s : Finset 𝔸) : Set 𝔸) (π • x) := by
  intro π' hπ'
  have := h (π⁻¹ * π' * π) ?_
  · rwa [mul_smul, mul_smul, inv_smul_eq_iff] at this
  intro a ha
  rw [mul_smul, mul_smul, inv_smul_eq_iff]
  apply hπ'
  rwa [smul_name_eq, Finset.mem_coe, Finset.mem_smul_iff, smul_name_eq, inv_apply_self]

theorem MulAction.Supports.of_smul' {α : Type*} [MulAction (Finperm 𝔸) α]
    {s : Finset 𝔸} {x : α} {π : Finperm 𝔸}
    (h : Supports (Finperm 𝔸) (s : Set 𝔸) (π • x)) :
    Supports (Finperm 𝔸) ((π⁻¹ • s : Finset 𝔸) : Set 𝔸) x := by
  have := h.smul' π⁻¹
  rwa [inv_smul_smul] at this

theorem FinitelySupported.smul {α : Type*} [MulAction (Finperm 𝔸) α] {x : α}
    (h : FinitelySupported 𝔸 x) (π : Finperm 𝔸) :
    FinitelySupported 𝔸 (π • x) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨π • s, hs.smul' π⟩

theorem FinitelySupported.of_smul {α : Type*} [MulAction (Finperm 𝔸) α] {x : α}
    {π : Finperm 𝔸} (h : FinitelySupported 𝔸 (π • x)):
    FinitelySupported 𝔸 x := by
  have := h.smul π⁻¹
  rwa [inv_smul_smul] at this

section Set
open scoped Pointwise

theorem Finset.smul_coe_eq_coe_iff {G α : Type*} [Group G] [MulAction G α]
    (g : G) (s : Finset α) :
    g • (s : Set α) = s ↔ g • s = s := by
  simp only [Set.ext_iff, Finset.mem_coe, Finset.ext_iff,
    Set.mem_smul_set_iff_inv_smul_mem, Finset.mem_smul_iff]

theorem Finset.supports_coe_iff {α : Type*} [MulAction (Finperm 𝔸) α] (s : Finset α) (t : Set 𝔸) :
    Supports (Finperm 𝔸) t (s : Set α) ↔ Supports (Finperm 𝔸) t s := by
  unfold Supports
  simp only [Finset.smul_coe_eq_coe_iff]

theorem Finset.coe_finitelySupported_iff {α : Type*} [MulAction (Finperm 𝔸) α] (s : Finset α) :
    FinitelySupported 𝔸 (s : Set α) ↔ FinitelySupported 𝔸 s := by
  simp only [FinitelySupported, supports_coe_iff]

theorem Set.finitelySupported_of_finite {α : Type*} [Nominal 𝔸 α] (s : Set α) (hs : s.Finite) :
    FinitelySupported 𝔸 s := by
  lift s to Finset α using hs
  rw [Finset.coe_finitelySupported_iff]
  apply Nominal.supported

omit [Infinite 𝔸] in
theorem FinitelySupported.compl {α : Type*} [MulAction (Finperm 𝔸) α]
    {s : Set α} (hs : FinitelySupported 𝔸 s) :
    FinitelySupported 𝔸 sᶜ := by
  obtain ⟨t, ht⟩ := hs
  refine ⟨t, ?_⟩
  intro π hπ
  rw [Set.smul_set_compl, ht π hπ]

end Set

set_option linter.unusedVariables false in
/-- A type alias to endow a type `α` with its discrete nominal structure. -/
def Discrete (𝔸 : Type*) (α : Type*) :=
  α

instance {α : Type*} : MulAction (Finperm 𝔸) (Discrete 𝔸 α) where
  smul _ := id
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance {α : Type*} : Nominal 𝔸 (Discrete 𝔸 α) where
  supported := λ _ ↦ ⟨∅, λ _ _ ↦ rfl⟩

class Equivariant (𝔸 : Type*) [DecidableEq 𝔸]
    {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (f : α → β) : Prop where
  smul_apply : ∀ π : Finperm 𝔸, ∀ a, π • f a = f (π • a)

attribute [simp] Equivariant.smul_apply

instance {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (f : Discrete 𝔸 α → Discrete 𝔸 β) :
    Equivariant 𝔸 f := by
  constructor
  intro π x
  rfl

instance {α : Type*} [MulAction (Finperm 𝔸) α] : Equivariant 𝔸 (supp 𝔸 : α → Finset 𝔸) := by
  constructor
  intro π x
  ext a
  rw [Finset.mem_smul_iff]
  by_cases hx : FinitelySupported 𝔸 x
  · rw [mem_supp_iff' x hx, mem_supp_iff' (π • x) (hx.smul π)]
    constructor
    · intro h s hs
      refine (Finset.mem_map' _).mp (h (π⁻¹ • s) ?_)
      have := hs.smul' π⁻¹
      rwa [inv_smul_smul] at this
    · intro h s hs
      have := h (π • s) (hs.smul' π)
      rwa [Finset.mem_smul_iff] at this
  · rw [supp_eq_of_not_finitelySupported x hx, supp_eq_of_not_finitelySupported]
    · simp only [smul_name_eq, Finset.not_mem_empty]
    · contrapose! hx
      exact hx.of_smul

theorem MulAction.Supports.map {α : Type*} [MulAction (Finperm 𝔸) α]
    {x : α} {s : Set 𝔸} (h : Supports (Finperm 𝔸) s x)
    {β : Type*} [MulAction (Finperm 𝔸) β] (f : α → β) [Equivariant 𝔸 f] :
    Supports (Finperm 𝔸) s (f x) := by
  intro π hπ
  rw [Equivariant.smul_apply, h π hπ]

theorem MulAction.Supports.of_map {α : Type*} [MulAction (Finperm 𝔸) α]
    {β : Type*} [MulAction (Finperm 𝔸) β]
    {x : α} {s : Set 𝔸} {f : α → β} [Equivariant 𝔸 f] (h : Supports (Finperm 𝔸) s (f x))
    (hf : Function.Injective f) :
    Supports (Finperm 𝔸) s x := by
  intro π hπ
  have := h π hπ
  rw [Equivariant.smul_apply] at this
  exact hf this

theorem FinitelySupported.map {α : Type*} [MulAction (Finperm 𝔸) α]
    {x : α} (h : FinitelySupported 𝔸 x)
    {β : Type*} [MulAction (Finperm 𝔸) β] (f : α → β) [Equivariant 𝔸 f] :
    FinitelySupported 𝔸 (f x) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, hs.map f⟩

theorem FinitelySupported.of_map {α : Type*} [MulAction (Finperm 𝔸) α]
    {β : Type*} [MulAction (Finperm 𝔸) β]
    {x : α} {f : α → β} [Equivariant 𝔸 f] (h : FinitelySupported 𝔸 (f x))
    (hf : Function.Injective f) :
    FinitelySupported 𝔸 x := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, hs.of_map hf⟩

theorem supp_apply_subset {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β]
    (f : α → β) [Equivariant 𝔸 f] (x : α) :
    supp 𝔸 (f x) ⊆ supp 𝔸 x := by
  intro a ha
  rw [Nominal.mem_supp_iff] at ha ⊢
  intro s hs
  exact ha s (hs.map f)

theorem supp_apply_eq_of_injective {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β]
    (f : α → β) [Equivariant 𝔸 f] (hf : Function.Injective f) (x : α) :
    supp 𝔸 (f x) = supp 𝔸 x := by
  apply subset_antisymm
  · exact supp_apply_subset f x
  intro a ha
  rw [Nominal.mem_supp_iff] at ha ⊢
  intro s hs
  exact ha s (hs.of_map hf)

theorem finitelySupported_of_surjective {α β : Type*} [Nominal 𝔸 α] [MulAction (Finperm 𝔸) β]
    (f : α → β) [Equivariant 𝔸 f] (hf : Function.Surjective f) (y : β) :
    FinitelySupported 𝔸 y := by
  obtain ⟨x, rfl⟩ := hf y
  exact (Nominal.supported x).map f

def nominal_of_surjective {α β : Type*} [Nominal 𝔸 α] [MulAction (Finperm 𝔸) β]
    (f : α → β) [Equivariant 𝔸 f] (hf : Function.Surjective f) :
    Nominal 𝔸 β where
  supported := finitelySupported_of_surjective f hf
