import Mathlib.Data.Finset.Card
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
theorem inv_apply_self [DecidableEq α] (π : Finperm α) (a : α) :
    π⁻¹ (π a) = a := by
  rw [← mul_apply, inv_mul_cancel, one_apply]

@[simp]
theorem apply_inv_self [DecidableEq α] (π : Finperm α) (a : α) :
    π (π⁻¹ a) = a := by
  rw [← mul_apply, mul_inv_cancel, one_apply]

theorem inv_eq_iff_eq [DecidableEq α] (π : Finperm α) (a b : α) :
    π⁻¹ a = b ↔ a = π b :=
  by aesop

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
  split_ifs <;> cc

theorem swap_triple' [DecidableEq α] (a b c : α) (h₁ : a ≠ b) (h₂ : b ≠ c) :
    swap a c = swap a b * swap a c * swap b c := by
  ext d
  simp only [swap_apply_def, mul_apply]
  split_ifs <;> cc

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

theorem not_mem_remove_support [DecidableEq α] (π : Finperm α) (a : α) :
    a ∉ (π.remove a).support := by
  rw [mem_support_iff, remove_apply]
  simp

theorem remove_support_ssubset [DecidableEq α] (π : Finperm α)
    (a : α) (ha : a ∈ π.support) :
    (π.remove a).support ⊂ π.support := by
  rw [ssubset_iff_subset_not_subset]
  refine ⟨π.remove_support_subset a, ?_⟩
  rw [Finset.not_subset]
  exact ⟨a, ha, π.not_mem_remove_support a⟩

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
      · apply not_mem_remove_support
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

end Finperm
