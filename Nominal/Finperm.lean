import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Defs

open Equiv

structure Finperm (α : Type*) extends Perm α where
  support : Finset α
  mem_support_iff' : ∀ a, a ∈ support ↔ toFun a ≠ a

namespace Finperm

variable {α : Type*}

theorem ext' {π₁ π₂ : Finperm α}
    (h₁ : π₁.toFun = π₂.toFun) (h₂ : π₁.invFun = π₂.invFun) : π₁ = π₂ := by
  obtain ⟨π₁, s₁, hs₁⟩ := π₁
  obtain ⟨π₂, s₂, hs₂⟩ := π₂
  cases Equiv.ext (congr_fun h₁)
  suffices s₁ = s₂ by simp only [this]
  ext a
  rw [hs₁, hs₂]

instance : EquivLike (Finperm α) α α where
  coe π := π.toFun
  inv π := π.invFun
  left_inv π := π.left_inv
  right_inv π := π.right_inv
  coe_injective' _ _ := ext'

theorem mem_support_iff (π : Finperm α) : ∀ a, a ∈ π.support ↔ π a ≠ a :=
  π.mem_support_iff'

@[ext]
theorem ext {π₁ π₂ : Finperm α} (h : ∀ a, π₁ a = π₂ a) : π₁ = π₂ :=
  DFunLike.ext π₁ π₂ h

@[simp]
theorem toEquiv_apply (π : Finperm α) (a : α) :
    π.toEquiv a = π a :=
  rfl

@[simp]
theorem toEquiv_symm (π : Finperm α) :
    π.toEquiv.symm = π.symm :=
  rfl

def ofSubset [DecidableEq α] (π : Perm α) (s : Finset α) (hs : ∀ a, π a ≠ a → a ∈ s) :
    Finperm α where
  support := s.filter (λ a ↦ π a ≠ a)
  mem_support_iff' := by aesop
  __ := π

theorem ofSubset_support_subset [DecidableEq α]
    {π : Perm α} {s : Finset α} {hs : ∀ a, π a ≠ a → a ∈ s} :
    (ofSubset π s hs).support ⊆ s :=
  Finset.filter_subset _ _

protected def refl (α : Type*) : Finperm α where
  support := ∅
  mem_support_iff' := by simp
  __ := Equiv.refl α

protected def symm (π : Finperm α) : Finperm α where
  support := π.support
  mem_support_iff' := by
    simp only [π.mem_support_iff]
    simp [symm_apply_eq, ne_comm]
  __ := π.toEquiv.symm

protected def trans [DecidableEq α] (π₁ π₂ : Finperm α) : Finperm α :=
  ofSubset (π₁.toEquiv.trans π₂) (π₁.support ∪ π₂.support) (by
    simp [mem_support_iff]
    intro a
    contrapose!
    rintro ⟨ha₁, ha₂⟩
    rw [ha₁, ha₂])

instance [DecidableEq α] : Group (Finperm α) where
  mul π₁ π₂ := π₂.trans π₁
  mul_assoc := by aesop
  one := Finperm.refl α
  one_mul := by aesop
  mul_one := by aesop
  inv π := π.symm
  inv_mul_cancel := by
    intro π
    ext
    apply π.symm_apply_eq.mpr rfl

theorem one_apply [DecidableEq α] (a : α) :
    (1 : Finperm α) a = a :=
  rfl

theorem mul_apply [DecidableEq α] (π₁ π₂ : Finperm α) (a : α) :
    (π₁ * π₂) a = π₁ (π₂ a) :=
  rfl

@[simp]
theorem coe_one [DecidableEq α] :
    ((1 : Finperm α) : α → α) = id :=
  rfl

@[simp]
theorem coe_mul [DecidableEq α] (π₁ π₂ : Finperm α) :
    ((π₁ * π₂) : α → α) = π₁ ∘ π₂ :=
  rfl

@[simp]
theorem one_support [DecidableEq α] :
    (1 : Finperm α).support = ∅ :=
  rfl

theorem mul_support_subset [DecidableEq α] (π₁ π₂ : Finperm α) :
    (π₁ * π₂).support ⊆ π₁.support ∪ π₂.support := by
  apply ofSubset_support_subset.trans (subset_of_eq (Finset.union_comm _ _))
  simp [mem_support_iff]
  intro a
  contrapose!
  rintro ⟨ha₁, ha₂⟩
  rw [ha₁, ha₂]

@[simp]
theorem inv_apply_self [DecidableEq α] (π : Finperm α) (a : α) :
    π⁻¹ (π a) = a := by
  rw [← mul_apply, inv_mul_cancel, one_apply]

@[simp]
theorem apply_inv_self [DecidableEq α] (π : Finperm α) (a : α) :
    π (π⁻¹ a) = a := by
  rw [← mul_apply, mul_inv_cancel, one_apply]

theorem inv_apply_eq_iff_eq [DecidableEq α] (π : Finperm α) (a b : α) :
    π⁻¹ a = b ↔ a = π b :=
  by aesop

@[simp]
theorem inv_support [DecidableEq α] (π : Finperm α) :
    π⁻¹.support = π.support :=
  rfl

@[simp]
theorem mk_apply (π : Perm α) (s : Finset α) (hs : ∀ a, a ∈ s ↔ π.toFun a ≠ a) (a : α) :
    (⟨π, s, hs⟩ : Finperm α) a = π a :=
  rfl

@[simp]
theorem mk_inv_apply [DecidableEq α] (π : Perm α) (s : Finset α)
    (hs : ∀ a, a ∈ s ↔ π.toFun a ≠ a) (a : α) :
    (⟨π, s, hs⟩ : Finperm α)⁻¹ a = π.symm a :=
  rfl

/-- Copy of a `Finperm` with a new `toFun` equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (π : Finperm α) (f g : α → α)
    (h₁ : f = π) (h₂ : g = π.invFun) : Finperm α where
  toFun := f
  invFun := g
  left_inv := h₁.symm ▸ h₂.symm ▸ π.left_inv
  right_inv := h₁.symm ▸ h₂.symm ▸ π.right_inv
  support := π.support
  mem_support_iff' := h₁.symm ▸ π.mem_support_iff'

@[simp]
theorem coe_copy (π : Finperm α) (f g : α → α)
    (h₁ : f = π) (h₂ : g = π.invFun) :
    (π.copy f g h₁ h₂ : α → α) = f :=
  rfl

def swap [DecidableEq α] (a b : α) : Finperm α where
  support := if a = b then ∅ else {a, b}
  mem_support_iff' := by aesop (add norm Equiv.swap_apply_def)
  __ := Equiv.swap a b

theorem swap_apply_def [DecidableEq α] (a b c : α) :
    swap a b c = if c = a then b else if c = b then a else c :=
  rfl

@[simp]
theorem swap_apply_left [DecidableEq α] (a b : α) :
    swap a b a = b := by
  simp [swap_apply_def]

@[simp]
theorem swap_apply_right [DecidableEq α] (a b : α) :
    swap a b b = a := by
  simp [swap_apply_def]

theorem swap_apply_of_ne_of_ne [DecidableEq α] {a b c : α} :
    c ≠ a → c ≠ b → swap a b c = c := by
  rw [swap_apply_def]
  aesop

@[simp]
theorem swap_self [DecidableEq α] (a : α) :
    swap a a = 1 := by
  ext
  rw [swap_apply_def]
  aesop

theorem swap_comm [DecidableEq α] (a b : α) :
    swap a b = swap b a := by
  ext
  rw [swap_apply_def, swap_apply_def]
  aesop

@[simp]
theorem swap_swap [DecidableEq α] (a b : α) :
    swap a b * swap a b = 1 := by
  ext
  simp only [mul_apply, swap_apply_def]
  aesop

@[simp]
theorem swap_swap_apply [DecidableEq α] (a b c : α) :
    swap a b (swap a b c) = c := by
  rw [← mul_apply, swap_swap, one_apply]

@[simp]
theorem swap_inv [DecidableEq α] (a b : α) :
    (swap a b)⁻¹ = swap a b := by
  rw [inv_eq_iff_mul_eq_one, swap_swap]

theorem swap_triple [DecidableEq α] (a b c : α) (h₁ : a ≠ b) (h₂ : b ≠ c) :
    swap a b = swap a c * swap b c * swap a c := by
  ext d
  simp only [swap_apply_def, mul_apply]
  aesop

theorem swap_triple' [DecidableEq α] (a b c : α) (h₁ : a ≠ b) (h₂ : b ≠ c) :
    swap a c = swap a b * swap a c * swap b c := by
  ext d
  simp only [swap_apply_def, mul_apply]
  aesop

theorem swap_pair [DecidableEq α] (a b c : α) (h₁ : a ≠ b) (h₂ : b ≠ c) :
    swap b c * swap a c = swap a c * swap a b := by
  rw [swap_triple a b c h₁ h₂, ← mul_assoc, ← mul_assoc, swap_swap, one_mul]

def remove [DecidableEq α] (π : Finperm α) (a : α) : Finperm α :=
  ofSubset (π * swap a (π⁻¹ a)) π.support (by
    intro b hb
    simp [swap_apply_def] at hb
    rw [mem_support_iff]
    contrapose! hb
    split_ifs with h₁ h₂
    · aesop
    · rw [← hb, ← hb, h₂, apply_inv_self]
    · aesop)

theorem remove_apply [DecidableEq α] (π : Finperm α) (a b : α) :
    π.remove a b = π (swap a (π⁻¹ a) b) :=
  rfl

theorem remove_mul_eq [DecidableEq α] (π : Finperm α) (a : α) :
    π.remove a * swap a (π⁻¹ a) = π := by
  ext
  rw [mul_apply, remove_apply, swap_swap_apply]

theorem remove_support_subset [DecidableEq α] (π : Finperm α) (a : α) :
    (π.remove a).support ⊆ π.support :=
  Finset.filter_subset _ _

theorem notMem_remove_support [DecidableEq α] (π : Finperm α) (a : α) :
    a ∉ (π.remove a).support := by
  rw [mem_support_iff, remove_apply]
  simp

theorem remove_support_ssubset [DecidableEq α] (π : Finperm α)
    (a : α) (ha : a ∈ π.support) :
    (π.remove a).support ⊂ π.support := by
  rw [ssubset_iff_subset_not_subset]
  refine ⟨π.remove_support_subset a, ?_⟩
  rw [Finset.not_subset]
  exact ⟨a, ha, π.notMem_remove_support a⟩

@[elab_as_elim]
theorem swap_induction_right [DecidableEq α] (p : Finperm α → Prop)
    (one : p 1) (swap : ∀ π a b, a ∉ π.support → a ≠ b → p π → p (π * swap a b)) :
    ∀ π, p π := by
  rintro ⟨π, s, hs⟩
  induction s using Finset.strongInduction generalizing π
  case H s ih =>
    cases s using Finset.induction
    case empty =>
      suffices π = Equiv.refl α by
        cases this
        exact one
      aesop
    case insert a s has _ =>
      rw [← remove_mul_eq ⟨π, insert a s, hs⟩ a]
      apply swap
      · apply notMem_remove_support
      · rw [mk_inv_apply, ne_eq, eq_symm_apply]
        exact (hs a).mp (s.mem_insert_self a)
      exact ih _
        (remove_support_ssubset ⟨π, insert a s, hs⟩ a (by simp))
        (remove ⟨π, insert a s, hs⟩ a)
        (mem_support_iff _)

@[elab_as_elim]
theorem swap_induction_left [DecidableEq α] (p : Finperm α → Prop)
    (one : p 1) (swap : ∀ π a b, a ∉ π.support → a ≠ b → p π → p (swap a b * π)) :
    ∀ π, p π := by
  have := swap_induction_right (p := λ π ↦ p π⁻¹) ?_ ?_
  · intro π
    have := this π⁻¹
    rwa [inv_inv] at this
  · aesop
  · aesop

theorem mul_swap [DecidableEq α] (π : Finperm α) (a b : α) :
    π * swap a b = swap (π a) (π b) * π := by
  ext c
  simp only [coe_mul, Function.comp_apply]
  by_cases ha : c = a
  · cases ha
    simp only [swap_apply_left]
  by_cases hb : c = b
  · cases hb
    simp only [swap_apply_right]
  rw [swap_apply_of_ne_of_ne ha hb, swap_apply_of_ne_of_ne]
  · simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
    exact ha
  · simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
    exact hb

theorem swap_mul [DecidableEq α] (π : Finperm α) (a b : α) :
    swap a b * π = π * swap (π⁻¹ a) (π⁻¹ b) := by
  rw [mul_swap, apply_inv_self, apply_inv_self]

def toPerm [DecidableEq α] (π : Finperm α) (s t : Finset α)
    (h : s.image π = t) :
    s ≃ t where
  toFun x := ⟨π x, h ▸ Finset.mem_image_of_mem π x.prop⟩
  invFun x := ⟨π⁻¹ x, by
    obtain ⟨y, hy⟩ := Finset.mem_image.mp (by simpa only [← h] using x.prop)
    rw [eq_comm, ← inv_apply_eq_iff_eq] at hy
    exact hy.2 ▸ hy.1⟩
  left_inv a := Subtype.val_injective (inv_apply_self π a)
  right_inv a := Subtype.val_injective (apply_inv_self π a)

@[simp]
theorem toPerm_apply [DecidableEq α] {π : Finperm α} {s t : Finset α}
    (h : s.image π = t) (a : s) :
    π.toPerm s t h a = π a :=
  rfl

/-!
# Multiple swaps
-/

def swapsFun [DecidableEq α] {s t : Finset α} (π : s ≃ t) (a : α) : α :=
  if h : a ∈ s then
    π ⟨a, h⟩
  else if h : a ∈ t then
    π.symm ⟨a, h⟩
  else
    a

theorem swapsFun_involutive [DecidableEq α] {s t : Finset α} (hst : Disjoint s t) (π : s ≃ t) :
    Function.Involutive (swapsFun π) := by
  intro a
  unfold swapsFun
  rw [Finset.disjoint_iff_ne] at hst
  by_cases hs : a ∈ s
  · simp only [hs, ↓reduceDIte, Finset.coe_mem, Subtype.coe_eta, symm_apply_apply,
      dite_eq_right_iff]
    intro h
    cases hst _ h _ (π ⟨a, hs⟩).prop rfl
  by_cases ht : a ∈ t
  · simp only [hs, ↓reduceDIte, ht, Finset.coe_mem, Subtype.coe_eta, apply_symm_apply]
  · simp only [hs, ↓reduceDIte, ht]

def swaps [DecidableEq α] {s t : Finset α} (hst : Disjoint s t) (π : s ≃ t) : Finperm α where
  toFun := swapsFun π
  invFun := swapsFun π
  left_inv := swapsFun_involutive hst π
  right_inv := swapsFun_involutive hst π
  support := s ∪ t
  mem_support_iff' := by
    intro a
    rw [Finset.disjoint_iff_ne] at hst
    simp only [Finset.mem_union, swapsFun, ne_eq]
    split_ifs with h₁ h₂
    · simp only [h₁, true_or, true_iff]
      intro h
      have := (π ⟨a, h₁⟩).prop
      rw [h] at this
      exact hst a h₁ a this rfl
    · simp only [h₁, h₂, or_true, true_iff]
      intro h
      have := (π.symm ⟨a, h₂⟩).prop
      rw [h] at this
      contradiction
    · tauto

@[simp]
theorem swaps_inv [DecidableEq α] {s t : Finset α} (hst : Disjoint s t) (π : s ≃ t) :
    (swaps hst π)⁻¹ = swaps hst π :=
  rfl

@[simp]
theorem swaps_support [DecidableEq α] {s t : Finset α} (hst : Disjoint s t) (π : s ≃ t) :
    (swaps hst π).support = s ∪ t :=
  rfl

@[simp]
theorem swaps_swaps [DecidableEq α] {s t : Finset α} (hst : Disjoint s t) (π : s ≃ t) :
    swaps hst π * swaps hst π = 1 := by
  rw [mul_eq_one_iff_eq_inv]
  rfl

theorem swaps_eq_of_mem₁ [DecidableEq α] {s t : Finset α} {hst : Disjoint s t} {π : s ≃ t}
    (a : α) (ha : a ∈ s) :
    swaps hst π a = π ⟨a, ha⟩ := by
  simp only [swaps, mk_apply, coe_fn_mk, swapsFun, ha, ↓reduceDIte]

theorem swaps_eq_of_mem₂ [DecidableEq α] {s t : Finset α} {hst : Disjoint s t} {π : s ≃ t}
    (a : α) (ha : a ∈ t) :
    swaps hst π a = π.symm ⟨a, ha⟩ := by
  rw [Finset.disjoint_iff_ne] at hst
  simp only [swaps, mk_apply, coe_fn_mk, swapsFun, ha, ↓reduceDIte, dite_eq_right_iff]
  intro ha'
  cases hst a ha' a ha rfl

theorem swaps_eq_of_notMem [DecidableEq α] {s t : Finset α} {hst : Disjoint s t} {π : s ≃ t}
    (a : α) (has : a ∉ s) (hat : a ∉ t) :
    swaps hst π a = a := by
  simp only [swaps, mk_apply, coe_fn_mk, swapsFun, has, ↓reduceDIte, hat]

/-!
# The homogeneity lemma

This is lemma 1.14 in the Nominal Sets book.
-/

noncomputable def diffEquiv [DecidableEq α] {s t : Finset α} (h : s.card = t.card) :
    (s \ t : Finset α) ≃ (t \ s : Finset α) :=
  Finset.equivOfCardEq (Finset.card_sdiff_comm h)

noncomputable def extendMap [DecidableEq α] {s t : Finset α} (π : s ≃ t) (a : α) : α :=
  if ha : a ∈ s then
    π ⟨a, ha⟩
  else if ha' : a ∈ t then
    diffEquiv (Finset.card_eq_of_equiv π.symm) ⟨a, Finset.mem_sdiff.mpr ⟨ha', ha⟩⟩
  else
    a

theorem extendMap_mem_iff₁ [DecidableEq α] {s t : Finset α} (π : s ≃ t) (a : α) :
    extendMap π a ∈ t ↔ a ∈ s := by
  unfold extendMap
  split_ifs with h₁ h₂
  · simp only [Finset.coe_mem, h₁]
  · have := (diffEquiv (Finset.card_eq_of_equiv π.symm)
      ⟨a, Finset.mem_sdiff.mpr ⟨h₂, h₁⟩⟩).prop
    rw [Finset.mem_sdiff] at this
    simp only [this.2, h₁]
  · simp only [h₂, h₁]

theorem extendMap_mem_iff₂ [DecidableEq α] {s t : Finset α} (π : s ≃ t) (a : α) :
    extendMap π a ∈ s ∧ extendMap π a ∉ t ↔ a ∈ t ∧ a ∉ s := by
  unfold extendMap
  split_ifs with h₁ h₂
  · simp only [Finset.coe_mem, not_true_eq_false, and_false, h₁]
  · have := (diffEquiv (Finset.card_eq_of_equiv π.symm)
      ⟨a, Finset.mem_sdiff.mpr ⟨h₂, h₁⟩⟩).prop
    rw [Finset.mem_sdiff] at this
    simp only [this, not_false_eq_true, and_self, h₂, h₁]
  · simp only [h₂, h₁]

theorem extendMap_mem_iff₃ [DecidableEq α] {s t : Finset α} (π : s ≃ t) (a : α) :
    extendMap π a ∉ s ∧ extendMap π a ∉ t ↔ a ∉ s ∧ a ∉ t := by
  unfold extendMap
  split_ifs with h₁ h₂
  · simp only [Finset.coe_mem, not_true_eq_false, and_false, h₁, false_and]
  · have := (diffEquiv (Finset.card_eq_of_equiv π.symm)
      ⟨a, Finset.mem_sdiff.mpr ⟨h₂, h₁⟩⟩).prop
    rw [Finset.mem_sdiff] at this
    simp only [this, not_true_eq_false, not_false_eq_true, and_true, h₁, h₂, and_false]
  · simp only [h₂, h₁]

theorem extendMap_bijective [DecidableEq α] {s t : Finset α} (π : s ≃ t) :
    Function.Bijective (extendMap π) := by
  constructor
  · intro a₁ a₂ h
    by_cases hsa₁ : a₁ ∈ s
    · have hsa₂ := (extendMap_mem_iff₁ π a₁).mpr hsa₁
      rw [h, extendMap_mem_iff₁ π a₂] at hsa₂
      unfold extendMap at h
      simp only [hsa₁, ↓reduceDIte, hsa₂, Subtype.val_inj, EmbeddingLike.apply_eq_iff_eq,
        Subtype.mk.injEq] at h
      exact h
    by_cases hta₁ : a₁ ∈ t
    · have ha₂ := (extendMap_mem_iff₂ π a₁).mpr ⟨hta₁, hsa₁⟩
      rw [h, extendMap_mem_iff₂ π a₂] at ha₂
      unfold extendMap at h
      simp only [hsa₁, ↓reduceDIte, hta₁, ha₂, Subtype.val_inj, EmbeddingLike.apply_eq_iff_eq,
        Subtype.mk.injEq] at h
      exact h
    · have ha₂ := (extendMap_mem_iff₃ π a₁).mpr ⟨hsa₁, hta₁⟩
      rw [h, extendMap_mem_iff₃ π a₂] at ha₂
      unfold extendMap at h
      simp only [hsa₁, ↓reduceDIte, hta₁, ha₂] at h
      exact h
  · intro a
    by_cases hat : a ∈ t
    · use π.symm ⟨a, hat⟩
      rw [extendMap, dif_pos (Finset.coe_mem (π.symm ⟨a, hat⟩)), apply_symm_apply]
    by_cases has : a ∈ s
    · have := ((diffEquiv (Finset.card_eq_of_equiv π.symm)).symm
        ⟨a, Finset.mem_sdiff.mpr ⟨has, hat⟩⟩).prop
      rw [Finset.mem_sdiff] at this
      use (diffEquiv (Finset.card_eq_of_equiv π.symm)).symm ⟨a, Finset.mem_sdiff.mpr ⟨has, hat⟩⟩
      rw [extendMap, dif_neg this.2, dif_pos this.1, apply_symm_apply]
    · use a
      rw [extendMap, dif_neg has, dif_neg hat]

noncomputable def extendPerm [DecidableEq α] {s t : Finset α} (π : s ≃ t) : Perm α :=
  Equiv.ofBijective (extendMap π) (extendMap_bijective π)

theorem extendPerm_notMem [DecidableEq α] {s t : Finset α} (π : s ≃ t)
    (a : α) (ha : extendPerm π a ≠ a) : a ∈ s ∪ t := by
  contrapose! ha
  simp only [Finset.mem_union, not_or] at ha
  simp only [extendPerm, ofBijective_apply, extendMap, ha, ↓reduceDIte]

noncomputable def extendFinperm [DecidableEq α] {s t : Finset α} (π : s ≃ t) : Finperm α :=
  ofSubset (extendPerm π) (s ∪ t) (extendPerm_notMem π)

/-- The homogeneity lemma: there is a `Finperm α` extending any given equivalence
of finite sets `s ≃ t`, acting as the identity outside `s ∪ t`. -/
theorem exists_extension [DecidableEq α] {s t : Finset α} (π : s ≃ t) :
    ∃ π' : Finperm α, (∀ (a : α) (ha : a ∈ s), π' a = π ⟨a, ha⟩) ∧
      (π'.support ⊆ s ∪ t) := by
  refine ⟨extendFinperm π, ?_, ?_⟩
  · intro a ha
    simp only [extendFinperm, ofSubset, extendPerm, ofBijective_apply, extendMap, ne_eq,
      mk_apply, ha, ↓reduceDIte]
  · intro a ha
    by_contra h
    simp only [Finset.mem_union, not_or] at h
    simp only [extendFinperm, ofSubset, extendPerm, ofBijective_apply, extendMap, ne_eq,
      Finset.mem_filter, Finset.mem_union, h, or_self, ↓reduceDIte, not_true_eq_false,
      and_self] at ha

def _root_.Function.Embedding.toEquivFinsetRange {α β : Type*} {s : Finset α} [DecidableEq β]
    (f : s ↪ β) :
    s ≃ s.attach.map f where
  toFun x := ⟨f x, by simp only [Finset.mem_map', Finset.mem_attach]⟩
  invFun x := s.attach.choose (λ y ↦ f y = x) <| by
    obtain ⟨x, hx⟩ := x
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [Finset.mem_attach, and_self, EmbeddingLike.apply_eq_iff_eq, true_and, imp_self,
      implies_true]
  left_inv x := by
    apply f.injective
    exact s.attach.choose_property (λ y ↦ f y = f x) _
  right_inv x := by
    apply Subtype.val_injective
    exact s.attach.choose_property (λ y ↦ f y = x) _

/-- The homogeneity lemma for injections: there is a `Finperm α` extending any given injection
of finite sets `s ↪ t`, acting as the identity outside `s ∪ t`. -/
theorem exists_extension' [DecidableEq α] {s t : Finset α} (f : s ↪ t) :
    ∃ π : Finperm α, (∀ (a : α) (ha : a ∈ s), π a = f ⟨a, ha⟩) ∧
      (π.support ⊆ s ∪ t) := by
  obtain ⟨π, h₁, h₂⟩ := exists_extension
    ((f.trans (Function.Embedding.subtype _)).toEquivFinsetRange)
  refine ⟨π, ?_, ?_⟩
  · intro a ha
    rw [h₁ a ha]
    rfl
  · intro a ha
    have := h₂ ha
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_attach, Function.Embedding.trans_apply,
      Function.Embedding.coe_subtype, true_and, Subtype.exists] at this
    rw [Finset.mem_union]
    obtain ha' | ⟨b, hb, rfl⟩ := this
    · exact Or.inl ha'
    · exact Or.inr (Finset.coe_mem (f ⟨b, hb⟩))

/-- Another useful statement of the homogeneity lemma: for any two finite sets `s, t`,
there is a finite permutation that maps `s` outside `t`, and is the identity on `t \ s`. -/
theorem exists_fresh [DecidableEq α] [Infinite α] (s t : Finset α) :
    ∃ π : Finperm α, (∀ a ∈ s, π a ∉ t) ∧ (∀ a ∈ t \ s, π a = a) := by
  induction s using Finset.cons_induction_on
  case empty =>
    use 1
    simp only [Finset.notMem_empty, coe_one, id_eq, IsEmpty.forall_iff, implies_true,
      Finset.sdiff_empty, and_self]
  case cons a s h ih =>
    obtain ⟨π, hπ₁, hπ₂⟩ := ih
    simp only [Finset.mem_sdiff, and_imp] at hπ₂
    obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (s ∪ t ∪ π.support)
    simp only [Finset.union_assoc, Finset.mem_union, mem_support_iff, ne_eq,
      not_or, Decidable.not_not] at hb
    refine ⟨π * swap a b, ?_, ?_⟩
    · intro c hc₁ hc₂
      rw [Finset.cons_eq_insert, Finset.mem_insert] at hc₁
      rw [coe_mul, Function.comp_apply] at hc₂
      obtain rfl | hc₁ := hc₁
      · rw [swap_apply_left, hb.2.2] at hc₂
        tauto
      · rw [swap_apply_of_ne_of_ne] at hc₂
        · have := hπ₁ c hc₁
          tauto
        · rintro rfl
          contradiction
        · rintro rfl
          tauto
    · intro c hc
      simp only [Finset.cons_eq_insert, Finset.mem_sdiff, Finset.mem_insert, not_or] at hc
      rw [coe_mul, Function.comp_apply, swap_apply_of_ne_of_ne, hπ₂ c hc.1 hc.2.2]
      · rintro rfl
        tauto
      · rintro rfl
        tauto

end Finperm
