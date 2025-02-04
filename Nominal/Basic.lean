import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Lattice
import Nominal.Finperm

/-!
We're working from <https://people.cs.nott.ac.uk/pszvc/mgs/MGS2011_nominal_sets.pdf>.
-/

variable {𝔸 : Type*} [DecidableEq 𝔸]

open Finperm

/-- A typeclass for types that have a `Finperm 𝔸`-action.
We use a different notation `⬝` in order to avoid conflicts with `Pi.perm`. -/
class HasPerm (𝔸 : Type*) (α : Sort*) where
  /-- Permute this type according to the given finite permutation of names. -/
  perm : Finperm 𝔸 → α → α

@[inherit_doc]
infixr:73 " ⬝ " => HasPerm.perm

/-! We do the same as Mathlib does for `⬝`: a trick to help some elaboration problems. -/
@[inherit_doc HasPerm.perm]
macro_rules | `($x ⬝ $y) => `(leftact% HasPerm.perm $x $y)

/-- A typeclass for types that have a lawful `Finperm 𝔸`-action. -/
class MulPerm (𝔸 : Type*) (α : Sort*) [DecidableEq 𝔸] extends HasPerm 𝔸 α where
  one_perm : ∀ x : α, (1 : Finperm 𝔸) ⬝ x = x
  mul_perm : ∀ π₁ π₂ : Finperm 𝔸, ∀ x : α, (π₁ * π₂) ⬝ x = π₁ ⬝ π₂ ⬝ x

export MulPerm (one_perm mul_perm)

attribute [simp] one_perm

theorem MulPerm.injective {α : Sort*} [MulPerm 𝔸 α] (π : Finperm 𝔸) :
    Function.Injective λ x : α ↦ π ⬝ x := by
  intro x y h
  have := congr_arg (π⁻¹ ⬝ ·) h
  simp only [← mul_perm, inv_mul_cancel, one_perm] at this
  exact this

@[simp]
theorem perm_left_cancel_iff {α : Sort*} [MulPerm 𝔸 α] (π : Finperm 𝔸) (x y : α) :
    π ⬝ x = π ⬝ y ↔ x = y :=
  (MulPerm.injective π).eq_iff

@[simp]
theorem inv_perm_perm {α : Sort*} [MulPerm 𝔸 α] (π : Finperm 𝔸) (x : α) :
    π⁻¹ ⬝ π ⬝ x = x := by
  have := mul_perm π⁻¹ π x
  rw [inv_mul_cancel, one_perm] at this
  rw [← this]

@[simp]
theorem perm_inv_perm {α : Sort*} [MulPerm 𝔸 α] (π : Finperm 𝔸) (x : α) :
    π ⬝ π⁻¹ ⬝ x = x := by
  have := mul_perm π π⁻¹ x
  rw [mul_inv_cancel, one_perm] at this
  rw [← this]

theorem perm_eq_iff_eq_inv_perm {α : Sort*} [MulPerm 𝔸 α] (π : Finperm 𝔸) (x y : α) :
    π ⬝ x = y ↔ x = π⁻¹ ⬝ y := by
  rw [← perm_left_cancel_iff π x (π⁻¹ ⬝ y), perm_inv_perm]

theorem inv_perm_eq_iff {α : Sort*} [MulPerm 𝔸 α] (π : Finperm 𝔸) (x y : α) :
    π⁻¹ ⬝ x = y ↔ x = π ⬝ y := by
  rw [← perm_left_cancel_iff π⁻¹ x (π ⬝ y), inv_perm_perm]

instance : MulPerm 𝔸 𝔸 where
  perm π a := π a
  one_perm := Finperm.one_apply
  mul_perm := Finperm.mul_apply

@[simp]
theorem Finperm.perm_name_eq (π : Finperm 𝔸) (a : 𝔸) :
    π ⬝ a = π a :=
  rfl

/-- A finite set of names `s` *supports* `x` if `π ⬝ x = x` whenever
`π a = a` for all `a ∈ s`. -/
def Supports {α : Sort*} [HasPerm 𝔸 α] (s : Finset 𝔸) (x : α) : Prop :=
  ∀ π : Finperm 𝔸, (∀ a ∈ s, π a = a) → π ⬝ x = x

omit [DecidableEq 𝔸] in
theorem Supports.mono {α : Sort*} [HasPerm 𝔸 α] {s t : Finset 𝔸} {x : α}
    (h : Supports s x) (h' : s ⊆ t) : Supports t x :=
  λ π hπ ↦ h π (λ a ha ↦ hπ a (h' ha))

theorem Finperm.supports_iff' (𝔸 : Type*) [DecidableEq 𝔸] {α : Sort*} [MulPerm 𝔸 α]
    (s : Finset 𝔸) (x : α) :
    Supports s x ↔ ∀ a b, a ∉ s → b ∉ s → swap a b ⬝ x = x := by
  constructor
  · intro hs a b ha hb
    apply hs (swap a b)
    intro c hc
    apply swap_apply_of_ne_of_ne <;>
    · rintro rfl
      contradiction
  · intro h π hπ
    induction π using swap_induction_right
    case one => rw [one_perm]
    case swap π a b ha hab ih =>
      rw [mem_support_iff, not_ne_iff] at ha
      rw [mul_perm]
      by_cases ha' : a ∈ s
      · have := hπ a ha'
        simp only [coe_mul, Function.comp_apply, swap_apply_left] at this
        have := ha.trans this.symm
        rw [EmbeddingLike.apply_eq_iff_eq] at this
        contradiction
      by_cases hb' : b ∈ s
      · have := hπ b hb'
        simp only [coe_mul, Function.comp_apply, swap_apply_right] at this
        have := ha.symm.trans this
        contradiction
      rw [h a b ha' hb']
      apply ih
      intro c hc
      have := hπ c hc
      rwa [mul_apply, swap_apply_of_ne_of_ne] at this <;>
      · rintro rfl; contradiction

theorem Finperm.supports_iff (𝔸 : Type*) [DecidableEq 𝔸] {α : Sort*} [MulPerm 𝔸 α]
    (s : Finset 𝔸) (x : α) :
    Supports s x ↔ ∀ a b, a ∉ s → b ∉ s → a ≠ b → swap a b ⬝ x = x := by
  rw [supports_iff']
  constructor
  · tauto
  · intro h a b ha hb
    by_cases hab : a = b
    · cases hab
      rw [swap_self, one_perm]
    · exact h a b ha hb hab

theorem Finperm.inter_supports [Infinite 𝔸] {α : Sort*} [MulPerm 𝔸 α]
    (s t : Finset 𝔸) (x : α)
    (hs : Supports s x) (ht : Supports t x) :
    Supports (s ∩ t) x := by
  rw [supports_iff'] at hs ht
  rw [supports_iff]
  intro a b ha hb hab
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset (s ∪ t ∪ {a, b})
  simp at hc
  rw [swap_triple a b c hab (by tauto), mul_perm, mul_perm]
  rw [Finset.mem_inter, not_and] at ha hb
  have : swap a c ⬝ x = x := by
    by_cases ha' : a ∈ s
    · exact ht a c (ha ha') (by tauto)
    · exact hs a c ha' (by tauto)
  have : swap b c ⬝ x = x := by
    by_cases hb' : b ∈ s
    · exact ht b c (hb hb') (by tauto)
    · exact hs b c hb' (by tauto)
  cc

/-!
# Finite and empty support
-/

/-- An object is called *equivariant* if it is fixed under all permutations of names. -/
def Equivariant (𝔸 : Type*) [DecidableEq 𝔸] {α : Sort*} [HasPerm 𝔸 α] (x : α) :=
  ∀ π : Finperm 𝔸, π ⬝ x = x

/-- An object is called *finitely supported* if it has a finite support. -/
def FinitelySupported (𝔸 : Type*) [DecidableEq 𝔸] {α : Sort*} [HasPerm 𝔸 α]
    (x : α) : Prop :=
  ∃ s : Finset 𝔸, Supports s x

theorem Equivariant.finitelySupported {α : Sort*} [HasPerm 𝔸 α] {x : α}
    (h : Equivariant 𝔸 x) : FinitelySupported 𝔸 x := by
  use ∅
  intro π _
  rw [h]

/-- The minimal support of an object, if it exists. -/
noncomputable def supp (𝔸 : Type*) [DecidableEq 𝔸] {α : Sort*} [MulPerm 𝔸 α] (x : α) :
    Finset 𝔸 :=
  open scoped Classical in
  if hx : FinitelySupported 𝔸 x then
    hx.choose.filter (λ a ↦ ∀ s : Finset 𝔸, Supports s x → a ∈ s)
  else
    ∅

theorem supp_eq_of_not_finitelySupported {α : Sort*} [MulPerm 𝔸 α]
    (x : α) (hx : ¬FinitelySupported 𝔸 x) :
    supp 𝔸 x = ∅ := by
  rw [supp, dif_neg hx]

theorem mem_supp_iff' {α : Sort*} [MulPerm 𝔸 α]
    (x : α) (hx : FinitelySupported 𝔸 x) (a : 𝔸) :
    a ∈ supp 𝔸 x ↔ ∀ s : Finset 𝔸, Supports s x → a ∈ s := by
  classical
  rw [supp, dif_pos hx, Finset.mem_filter, and_iff_right_iff_imp]
  intro ha
  exact ha hx.choose hx.choose_spec

theorem supp_supports' [Infinite 𝔸] {α : Sort*} [MulPerm 𝔸 α]
    (x : α) (hx : FinitelySupported 𝔸 x) :
    Supports (supp 𝔸 x) x := by
  intro π hπ
  obtain ⟨s, hs⟩ := hx
  induction s using Finset.strongInduction
  case H s ih =>
    by_cases ht : ∃ t ⊂ s, Supports t x
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

theorem supp_minimal {α : Sort*} [MulPerm 𝔸 α]
    (x : α) (s : Finset 𝔸) (hs : Supports s x) :
    supp 𝔸 x ⊆ s := by
  intro a ha
  rw [mem_supp_iff' x ⟨s, hs⟩] at ha
  exact ha s hs

class Nominal (𝔸 : Type*) [DecidableEq 𝔸] (α : Sort*)
    extends MulPerm 𝔸 α where
  supported : ∀ x : α, FinitelySupported 𝔸 x

namespace Nominal

instance : Nominal 𝔸 𝔸 where
  supported := λ a ↦ ⟨{a}, λ _ hπ ↦ hπ a (Finset.mem_singleton_self a)⟩

theorem mem_supp_iff {α : Sort*} [Nominal 𝔸 α]
    (x : α) (a : 𝔸) :
    a ∈ supp 𝔸 x ↔ ∀ s : Finset 𝔸, Supports s x → a ∈ s :=
  mem_supp_iff' x (Nominal.supported x) a

theorem supp_supports (𝔸 : Type*) [DecidableEq 𝔸] [Infinite 𝔸] {α : Sort*} [Nominal 𝔸 α] (x : α) :
    Supports (supp 𝔸 x) x :=
  supp_supports' x (Nominal.supported x)

theorem supp_subset_iff [Infinite 𝔸] {α : Sort*} [Nominal 𝔸 α] (x : α) (s : Finset 𝔸) :
    supp 𝔸 x ⊆ s ↔ Supports s x :=
  ⟨(supp_supports 𝔸 x).mono, supp_minimal x s⟩

@[simp]
theorem name_supp_eq [Infinite 𝔸] (a : 𝔸) :
    supp 𝔸 a = {a} := by
  ext b
  rw [mem_supp_iff]
  constructor
  · intro h
    exact h {a} (λ _ hπ ↦ hπ a (Finset.mem_singleton_self a))
  · intro h
    rw [Finset.mem_singleton] at h
    cases h
    intro s hs
    by_contra ha
    obtain ⟨b, hb⟩ := Infinite.exists_not_mem_finset (s ∪ {a})
    rw [Finset.mem_union, Finset.mem_singleton, not_or] at hb
    have := hs (swap a b) ?_
    · rw [perm_name_eq, swap_apply_left] at this
      tauto
    · intro c hc
      apply swap_apply_of_ne_of_ne <;> aesop

end Nominal

instance {α : Type*} [MulPerm 𝔸 α] : HasPerm 𝔸 (Finset α) where
  perm π s := s.map ⟨(π ⬝ ·), MulPerm.injective π⟩

theorem Finset.perm_def {α : Type*} [MulPerm 𝔸 α]
    (π : Finperm 𝔸) (s : Finset α) :
    π ⬝ s = s.map ⟨(π ⬝ ·), MulPerm.injective π⟩ :=
  rfl

theorem Finset.mem_perm_iff {α : Type*} [MulPerm 𝔸 α]
    (π : Finperm 𝔸) (x : α) (s : Finset α) :
    x ∈ π ⬝ s ↔ π⁻¹ ⬝ x ∈ s := by
  rw [Finset.perm_def]
  aesop

instance {α : Type*} [MulPerm 𝔸 α] : MulPerm 𝔸 (Finset α) where
  one_perm _ := by
    ext
    simp [Finset.mem_perm_iff]
  mul_perm _ _ _ := by
    ext
    simp [Finset.mem_perm_iff, mul_perm]

theorem Finset.perm_eq_of_perm_eq {α : Type*} [MulPerm 𝔸 α]
    (s : Finset α) (π : Finperm 𝔸) (h : ∀ a ∈ s, π ⬝ a = a) :
    π ⬝ s = s := by
  ext a
  rw [Finset.mem_perm_iff]
  constructor
  · intro ha
    have := h _ ha
    rw [perm_inv_perm] at this
    rwa [← this] at ha
  · intro ha
    have := h _ ha
    rw [perm_eq_iff_eq_inv_perm] at this
    rwa [this] at ha

theorem Finset.finitelySupported [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (s : Finset α) :
    FinitelySupported 𝔸 s := by
  use s.biUnion (supp 𝔸)
  intro π hπ
  apply Finset.perm_eq_of_perm_eq
  intro x hx
  apply Nominal.supp_supports 𝔸 x
  aesop

instance [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] : Nominal 𝔸 (Finset α) where
  supported := Finset.finitelySupported

theorem Supports.perm {α : Sort*} [MulPerm 𝔸 α]
    {s : Finset 𝔸} {x : α}
    (h : Supports s x) (π : Finperm 𝔸) :
    Supports (π ⬝ s) (π ⬝ x) := by
  intro π' hπ'
  have := h (π⁻¹ * π' * π) ?_
  · rwa [mul_perm, mul_perm, inv_perm_eq_iff] at this
  intro a ha
  rw [coe_mul, Function.comp_apply, coe_mul, Function.comp_apply, hπ' (π a), inv_apply_self]
  rwa [Finset.mem_perm_iff, perm_name_eq, inv_apply_self]

theorem Supports.of_perm {α : Sort*} [MulPerm 𝔸 α]
    {s : Finset 𝔸} {x : α} {π : Finperm 𝔸}
    (h : Supports s (π ⬝ x)) :
    Supports (π⁻¹ ⬝ s) x := by
  have := h.perm π⁻¹
  rwa [inv_perm_perm] at this

theorem FinitelySupported.perm {α : Sort*} [MulPerm 𝔸 α] {x : α}
    (h : FinitelySupported 𝔸 x) (π : Finperm 𝔸) :
    FinitelySupported 𝔸 (π ⬝ x) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨π ⬝ s, hs.perm π⟩

theorem FinitelySupported.of_perm {α : Sort*} [MulPerm 𝔸 α] {x : α}
    {π : Finperm 𝔸} (h : FinitelySupported 𝔸 (π ⬝ x)):
    FinitelySupported 𝔸 x := by
  have := h.perm π⁻¹
  rwa [inv_perm_perm] at this

@[simp]
theorem Nominal.supp_perm_eq {α : Sort*} [Nominal 𝔸 α] (x : α) (π : Finperm 𝔸) :
    supp 𝔸 (π ⬝ x) = π ⬝ (supp 𝔸 x) := by
  ext a
  simp only [mem_supp_iff, Finset.mem_perm_iff]
  constructor
  · intro h s hs
    have := h _ (hs.perm π)
    rwa [Finset.mem_perm_iff] at this
  · intro h s hs
    have := h (π⁻¹ ⬝ s) ?_
    · rwa [Finset.mem_perm_iff, inv_inv, perm_name_eq, perm_name_eq, apply_inv_self] at this
    · have := hs.perm π⁻¹
      rwa [inv_perm_perm] at this

def StrongSupports {α : Sort*} [MulPerm 𝔸 α] (s : Finset 𝔸) (x : α) :=
  ∀ π : Finperm 𝔸, (∀ a ∈ s, π a = a) ↔ π ⬝ x = x

theorem StrongSupports.supports {α : Sort*} [MulPerm 𝔸 α]
    {s : Finset 𝔸} {x : α} (h : StrongSupports s x) : Supports s x := by
  intro π h'
  rwa [← h]

theorem subset_of_strongSupports [Infinite 𝔸] {s t : Finset 𝔸} {α : Sort*} [MulPerm 𝔸 α] {x : α}
    (hs : StrongSupports s x)
    (ht : Supports t x) :
    s ⊆ t := by
  intro a ha
  by_contra ha'
  obtain ⟨b, hb⟩ := Infinite.exists_not_mem_finset (t ∪ {a})
  rw [StrongSupports] at hs
  have := ht (swap a b) ?_
  · have := (hs (swap a b)).mpr this a ha
    aesop
  · intro c hc
    rw [swap_apply_of_ne_of_ne] <;> aesop

theorem supp_eq_of_strongSupports [Infinite 𝔸] {α : Sort*} [MulPerm 𝔸 α]
    (x : α) (s : Finset 𝔸) (hs : StrongSupports s x) :
    supp 𝔸 x = s := by
  apply subset_antisymm
  · apply supp_minimal x s hs.supports
  intro a ha
  rw [mem_supp_iff' x ⟨s, hs.supports⟩]
  intro t ht
  exact subset_of_strongSupports hs ht ha

theorem Nominal.mem_supp_iff_names_infinite [Infinite 𝔸] {α : Sort*} [Nominal 𝔸 α] (x : α) (a : 𝔸) :
    a ∈ supp 𝔸 x ↔ {b | swap a b ⬝ x ≠ x}.Infinite := by
  constructor
  · intro h
    by_contra h'
    rw [Set.not_infinite] at h'
    obtain ⟨t, ht⟩ := h'.exists_finset
    clear h'
    rw [mem_supp_iff] at h
    have := h t ?_
    · rw [ht] at this
      simp at this
    · rw [supports_iff]
      intro b c hb hc hbc
      rw [ht, Set.mem_setOf_eq, not_not] at hb hc
      by_cases hac : c = a
      · subst hac
        rw [swap_comm, hb]
      · rw [swap_triple b c a hbc hac, mul_perm, mul_perm, swap_comm b, swap_comm c, hb, hc, hb]
  · intro h
    contrapose h
    rw [Set.not_infinite]
    apply (supp 𝔸 x ∪ {a}).finite_toSet.subset
    intro b hb
    by_contra hb'
    have := supp_supports 𝔸 x
    rw [supports_iff] at this
    exact hb (this a b h (by aesop) (by aesop))

theorem Nominal.swap_perm_eq_of_swap_perm_eq [Infinite 𝔸] {α : Sort*} [Nominal 𝔸 α]
    (x : α) (a b c : 𝔸) (hbc : b ≠ c) (hca : c ≠ a) :
    swap a b ⬝ x = swap a c ⬝ x → swap a b ⬝ x = swap b c ⬝ x := by
  have := swap_triple b c a hbc hca
  rw [swap_comm b a, swap_comm c a] at this
  rw [this, mul_perm, mul_perm, perm_left_cancel_iff, ← inv_perm_eq_iff, swap_inv]
  tauto

theorem Nominal.swap_perm_injOn [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (x : α)
    (a : 𝔸) (ha : a ∈ supp 𝔸 x) :
    Set.InjOn (swap a · ⬝ x) ({b | swap a b ⬝ x ≠ x} \ supp 𝔸 x) := by
  intro b ⟨hb₁, hb₂⟩ c ⟨hc₁, hc₂⟩ h
  by_contra hbc
  have h' := Nominal.swap_perm_eq_of_swap_perm_eq x a b c (by aesop) (by aesop) h
  have := Nominal.supp_supports 𝔸 x
  rw [supports_iff] at this
  rw [this b c hb₂ hc₂ hbc] at h'
  exact hb₁ h'

/-- TODO: This is not in the source material. -/
theorem Nominal.mem_supp_iff_range_infinite [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α]
    (x : α) (a : 𝔸) :
    a ∈ supp 𝔸 x ↔ (Set.range (swap a · ⬝ x)).Infinite := by
  constructor
  · intro ha
    apply Set.infinite_of_injOn_mapsTo (swap_perm_injOn x a ha)
    · intro b _
      use b
    · apply Set.Infinite.diff
      · rwa [mem_supp_iff_names_infinite] at ha
      · exact Finset.finite_toSet (supp 𝔸 x)
  · intro ha
    rw [mem_supp_iff_names_infinite]
    contrapose ha
    rw [Set.not_infinite] at ha ⊢
    have := (ha.image (swap a · ⬝ x)).union (Set.finite_singleton x)
    apply this.subset
    rintro _ ⟨b, rfl⟩
    by_cases swap a b ⬝ x = x <;> aesop

theorem Finset.subset_supp [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (s : Finset α)
    (x : α) (hx : x ∈ s) :
    supp 𝔸 x ⊆ supp 𝔸 s := by
  intro a ha
  rw [Nominal.mem_supp_iff_range_infinite] at ha ⊢
  contrapose ha
  rw [Set.not_infinite] at ha ⊢
  have := ha.biUnion (t := λ t ↦ (t : Set α)) (λ _ _ ↦ finite_toSet _)
  apply this.subset
  rintro _ ⟨b, rfl⟩
  simp only [Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq', Set.mem_iUnion, mem_coe]
  use b
  rwa [Finset.mem_perm_iff, inv_perm_perm]

theorem Finset.supp_subset [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (s : Finset α) :
    supp 𝔸 s ⊆ s.biUnion (supp 𝔸) := by
  intro a ha
  contrapose ha
  simp only [mem_biUnion, not_exists, not_and,
    Nominal.mem_supp_iff_range_infinite, Set.not_infinite] at ha
  have := (finite_toSet _).biUnion ha
  rw [Nominal.mem_supp_iff_range_infinite, Set.not_infinite]
  apply (this.powerset.preimage (f := Finset.toSet) (λ _ _ _ _ ↦ coe_inj.mp)).subset
  rintro _ ⟨b, rfl⟩
  simp only [mem_coe, Set.mem_preimage, Set.mem_powerset_iff]
  rintro x hx
  rw [mem_coe, Finset.mem_perm_iff] at hx
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨_, hx, b, by rw [perm_inv_perm]⟩

theorem Finset.supp_eq [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (s : Finset α) :
    supp 𝔸 s = s.biUnion (supp 𝔸) := by
  apply subset_antisymm
  · exact supp_subset s
  · intro a ha
    rw [mem_biUnion] at ha
    obtain ⟨x, hx, ha⟩ := ha
    exact subset_supp s x hx ha

theorem Finset.supports_iff [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (s : Finset α) (t : Finset 𝔸) :
    Supports t s ↔ ∀ x ∈ s, Supports t x := by
  simp only [← Nominal.supp_subset_iff, Finset.supp_eq, biUnion_subset_iff_forall_subset]

/-!
# Propositions
-/

instance : MulPerm 𝔸 Prop where
  perm _ p := p
  one_perm _ := rfl
  mul_perm _ _ _ := rfl

instance (p : Prop) : Equivariant 𝔸 p :=
  λ _ ↦ rfl

@[simp]
theorem perm_prop (π : Finperm 𝔸) (p : Prop) :
    π ⬝ p ↔ p :=
  Iff.rfl

/-!
# Function types
-/

instance {α β : Sort*} [HasPerm 𝔸 α] [HasPerm 𝔸 β] :
    HasPerm 𝔸 (α → β) where
  perm π f x := π ⬝ f (π⁻¹ ⬝ x)

@[simp]
theorem Function.perm_def {α β : Sort*} [HasPerm 𝔸 α] [HasPerm 𝔸 β]
    (f : α → β) (x : α) (π : Finperm 𝔸) :
    (π ⬝ f) x = π ⬝ f (π⁻¹ ⬝ x) :=
  rfl

instance {α β : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    MulPerm 𝔸 (α → β) where
  one_perm f := by
    ext x
    rw [Function.perm_def, inv_one, one_perm, one_perm]
  mul_perm π₁ π₂ f := by
    ext x
    simp only [Function.perm_def, mul_inv_rev, mul_perm]

theorem Function.equivariant_iff {α β : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    (f : α → β) :
    Equivariant 𝔸 f ↔ ∀ π : Finperm 𝔸, ∀ x, π ⬝ f x = f (π ⬝ x) := by
  simp only [Equivariant, funext_iff, perm_def]
  constructor
  · intro h π x
    have := h π (π ⬝ x)
    rw [inv_perm_perm] at this
    rw [← this]
  · intro h π x
    rw [← h π⁻¹ x, perm_inv_perm]

theorem apply_perm_eq {α β : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] {f : α → β}
    (h : Equivariant 𝔸 f) (π : Finperm 𝔸) (x : α) :
    π ⬝ f x = f (π ⬝ x) := by
  rw [Function.equivariant_iff] at h
  rw [h]

theorem apply₂_perm_eq {α β γ : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ] {f : α → β → γ}
    (h : Equivariant 𝔸 f) (π : Finperm 𝔸) (x : α) (y : β) :
    π ⬝ f x y = f (π ⬝ x) (π ⬝ y) := by
  simp only [Function.equivariant_iff, funext_iff, Function.perm_def] at h
  have := h π x (π ⬝ y)
  rwa [inv_perm_perm] at this

theorem apply₃_perm_eq {α β γ δ : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ] [MulPerm 𝔸 δ]
    {f : α → β → γ → δ} (h : Equivariant 𝔸 f) (π : Finperm 𝔸) (x : α) (y : β) (z : γ) :
    π ⬝ f x y z = f (π ⬝ x) (π ⬝ y) (π ⬝ z) := by
  simp only [Function.equivariant_iff, funext_iff, Function.perm_def] at h
  have := h π x (π ⬝ y) (π ⬝ z)
  rwa [inv_perm_perm, inv_perm_perm] at this

theorem Function.supports_iff {α β : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    (f : α → β) (s : Finset 𝔸) :
    Supports s f ↔
      ∀ π : Finperm 𝔸, (∀ a ∈ s, π a = a) →
      ∀ x, π ⬝ f x = f (π ⬝ x) := by
  simp only [FinitelySupported, Supports, funext_iff, perm_def]
  constructor
  · intro hs π hπ x
    rw [← hs π⁻¹, perm_inv_perm, inv_inv]
    intro a ha
    conv_lhs => rw [← hπ a ha, inv_apply_self]
  · intro hs π hπ x
    rw [hs π hπ, perm_inv_perm]

theorem Function.finitelySupported_iff {α β : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    (f : α → β) :
    FinitelySupported 𝔸 f ↔
      ∃ s : Finset 𝔸, ∀ π : Finperm 𝔸, (∀ a ∈ s, π a = a) →
      ∀ x, π ⬝ f x = f (π ⬝ x) := by
  simp only [FinitelySupported, supports_iff]
