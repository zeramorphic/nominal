import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Data.Part
import Nominal.Fresh

open Finperm

variable {𝔸 : Type*} [DecidableEq 𝔸]

/-!
# Discrete structures
-/

set_option linter.unusedVariables false in
/-- A type alias to endow a type `α` with its discrete nominal structure. -/
def Discrete (𝔸 : Type*) (α : Sort*) :=
  α

instance {α : Sort*} : MulPerm 𝔸 (Discrete 𝔸 α) where
  perm _ := id
  one_perm _ := rfl
  mul_perm _ _ _ := rfl

instance {α : Sort*} : Nominal 𝔸 (Discrete 𝔸 α) where
  supported _ := ⟨∅, λ _ _ ↦ rfl⟩

/-- Typeclass for discrete nominal structures. -/
class IsDiscrete (𝔸 : Type*) [DecidableEq 𝔸] (α : Sort*) [HasPerm 𝔸 α] : Prop where
  perm_eq' : ∀ π : Finperm 𝔸, ∀ x : α, π ⬝ x = x

@[simp]
theorem IsDiscrete.perm_eq {α : Sort*} [HasPerm 𝔸 α] [IsDiscrete 𝔸 α] :
    ∀ π : Finperm 𝔸, ∀ x : α, π ⬝ x = x :=
  IsDiscrete.perm_eq'

instance {α : Sort*} : IsDiscrete 𝔸 (Discrete 𝔸 α) where
  perm_eq' _ _ := rfl

instance {α : Sort*} [Subsingleton α] [HasPerm 𝔸 α] : IsDiscrete 𝔸 α where
  perm_eq' _ _ := Subsingleton.elim _ _

instance : IsDiscrete 𝔸 Prop where
  perm_eq' _ _ := rfl

theorem equivariant_of_isDiscrete {α : Sort*} [HasPerm 𝔸 α] [IsDiscrete 𝔸 α] (x : α) :
    Equivariant 𝔸 x := by
  intro π
  rw [IsDiscrete.perm_eq]

theorem finitelySupported_of_isDiscrete {α : Sort*} [HasPerm 𝔸 α] [IsDiscrete 𝔸 α] (x : α) :
    FinitelySupported 𝔸 x :=
  (equivariant_of_isDiscrete x).finitelySupported

instance {α β : Sort*} [HasPerm 𝔸 α] [IsDiscrete 𝔸 α] [HasPerm 𝔸 β] [IsDiscrete 𝔸 β] :
    IsDiscrete 𝔸 (α → β) := by
  constructor
  intro π f
  ext x
  rw [Function.perm_def, IsDiscrete.perm_eq, IsDiscrete.perm_eq]

theorem Equivariant.not {α : Sort*} [MulPerm 𝔸 α] {p : α → Prop}
    (h : Equivariant 𝔸 p) :
    Equivariant 𝔸 (λ x ↦ ¬p x) :=
  (equivariant_of_isDiscrete (¬ ·)).comp h

theorem Equivariant.not₂ {α β : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] {p : α → β → Prop}
    (h : Equivariant 𝔸 p) :
    Equivariant 𝔸 (λ x y ↦ ¬p x y) :=
  (equivariant_of_isDiscrete (¬ ·)).comp₂ h

theorem FinitelySupported.not {α : Sort*} [MulPerm 𝔸 α] {p : α → Prop}
    (h : FinitelySupported 𝔸 p) :
    FinitelySupported 𝔸 (λ x ↦ ¬p x) :=
  (finitelySupported_of_isDiscrete (¬ ·)).comp h

theorem equivariant_iff_supp_eq_empty [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (x : α) :
    Equivariant 𝔸 x ↔ supp 𝔸 x = ∅ := by
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro a ha
    rw [Nominal.mem_supp_iff] at ha
    have := ha ∅ (λ π _ ↦ h π)
    cases this
  · intro h π
    have := Nominal.supp_supports 𝔸 x
    rw [h] at this
    exact this π (λ _ h ↦ by cases h)

theorem Equivariant.map {α : Type*} [MulPerm 𝔸 α] {x : α} (h : Equivariant 𝔸 x)
    {β : Type*} [MulPerm 𝔸 β]
    {f : α → β} (hf : Equivariant 𝔸 f) :
    Equivariant 𝔸 (f x) := by
  intro π
  rw [apply_perm_eq hf, h]

theorem Equivariant.apply_equivariant_of_isDiscrete
    {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] [IsDiscrete 𝔸 α]
    {f : α → β} (hf : Equivariant 𝔸 f) (x : α) :
    Equivariant 𝔸 (f x) :=
  (equivariant_of_isDiscrete x).map hf

/-- One part of the adjunction between the discrete and global sections functors. -/
def liftDiscrete {α β : Type*} [MulPerm 𝔸 β] (f : α → β)
    (_hf : ∀ x, Equivariant 𝔸 (f x)) :
    Discrete 𝔸 α → β :=
  f

theorem liftDiscrete_equivariant {α β : Type*} [MulPerm 𝔸 β] (f : α → β)
    (hf : ∀ x, Equivariant 𝔸 (f x)) :
    Equivariant 𝔸 (liftDiscrete f hf) := by
  intro π
  ext x
  rw [Function.perm_def, IsDiscrete.perm_eq π⁻¹ x, liftDiscrete, hf]

/-!
# Option and Part
-/

instance {α : Type*} [HasPerm 𝔸 α] : HasPerm 𝔸 (Part α) where
  perm π x := x.map (π ⬝ ·)

omit [DecidableEq 𝔸] in
theorem Part.perm_def {α : Type*} [HasPerm 𝔸 α] (π : Finperm 𝔸) (x : Part α) :
    π ⬝ x = x.map (π ⬝ ·) :=
  rfl

@[simp]
theorem Part.mem_perm_iff {α : Type*} [MulPerm 𝔸 α] (π : Finperm 𝔸) (x : Part α) (y : α) :
    y ∈ π ⬝ x ↔ π⁻¹ ⬝ y ∈ x := by
  rw [Part.perm_def, Part.mem_map_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [inv_perm_perm]
  · intro h
    use π⁻¹ ⬝ y
    rw [perm_inv_perm]
    exact ⟨h, rfl⟩

instance {α : Type*} [MulPerm 𝔸 α] : MulPerm 𝔸 (Part α) where
  one_perm := by
    intro x
    ext y
    simp only [Part.mem_perm_iff, inv_one, one_perm]
  mul_perm := by
    intro π₁ π₂ x
    ext y
    simp only [Part.mem_perm_iff, inv_one, mul_inv_rev, mul_perm]

theorem Part.supports_iff_of_dom {α : Type*} [MulPerm 𝔸 α]
    {x : Part α} (hx : x.Dom) (s : Finset 𝔸) :
    Supports s x ↔ Supports s (x.get hx) := by
  constructor
  · intro h π hπ
    have := congr_arg (x.get hx ∈ ·) (h π hπ)
    simp only [mem_perm_iff, eq_iff_iff] at this
    have := this.mpr (Part.get_mem hx)
    have := Part.get_eq_of_mem this hx
    rwa [perm_eq_iff_eq_inv_perm]
  · intro h π hπ
    have := h π hπ
    ext y
    rw [mem_perm_iff]
    constructor
    · intro h'
      rw [Part.get_eq_of_mem h' hx] at this
      rw [perm_inv_perm] at this
      rwa [← this] at h'
    · intro h'
      rw [Part.get_eq_of_mem h' hx, perm_eq_iff_eq_inv_perm] at this
      rwa [this] at h'

theorem Part.supports_of_not_dom {α : Type*} [MulPerm 𝔸 α]
    {x : Part α} (hx : ¬x.Dom) (s : Finset 𝔸) :
    Supports s x := by
  intro π hπ
  ext y
  rw [Part.eq_none_iff'.mpr hx]
  simp only [mem_perm_iff, Part.not_mem_none]

instance {α : Type*} [Nominal 𝔸 α] : Nominal 𝔸 (Part α) where
  supported := by
    rintro ⟨p, x⟩
    by_cases hp : p
    · obtain ⟨s, hs⟩ := Nominal.supported (𝔸 := 𝔸) (x hp)
      use s
      rwa [Part.supports_iff_of_dom]
    · use ∅
      exact Part.supports_of_not_dom hp ∅

theorem Part.supp_eq_of_dom {α : Type*} [Nominal 𝔸 α] {x : Part α} (hx : x.Dom) :
    supp 𝔸 x = supp 𝔸 (x.get hx) := by
  ext a
  simp only [Nominal.mem_supp_iff, supports_iff_of_dom hx]

theorem Part.supp_eq_of_not_dom {α : Type*} [Nominal 𝔸 α] {x : Part α} (hx : ¬x.Dom) :
    supp 𝔸 x = ∅ := by
  ext a
  simp only [Nominal.mem_supp_iff, supports_of_not_dom hx, forall_const, Finset.not_mem_empty,
    iff_false, not_forall]
  use ∅
  exact Finset.not_mem_empty a

theorem Part.fresh_iff_of_dom {α β : Type*} [Nominal 𝔸 α] [MulPerm 𝔸 β]
    {x : Part α} (hx : x.Dom) (y : β) :
    y #[𝔸] x ↔ y #[𝔸] x.get hx := by
  rw [fresh_def, fresh_def, supp_eq_of_dom hx]

theorem Part.fresh_of_not_dom {α β : Type*} [Nominal 𝔸 α]
    [MulPerm 𝔸 β] {x : Part α} (hx : ¬x.Dom) (y : β) :
    y #[𝔸] x := by
  rw [fresh_def, supp_eq_of_not_dom hx]
  exact Finset.disjoint_empty_right _

/-!
# Binary coproducts
-/

instance {α β : Type*} [HasPerm 𝔸 α] [HasPerm 𝔸 β] : HasPerm 𝔸 (α ⊕ β) where
  perm π x := x.elim (λ x ↦ .inl (π ⬝ x)) (λ x ↦ .inr (π ⬝ x))

omit [DecidableEq 𝔸] in
@[simp]
theorem Sum.perm_inl {α β : Type*} [HasPerm 𝔸 α] [HasPerm 𝔸 β] (π : Finperm 𝔸) (x : α) :
    (π ⬝ .inl x : α ⊕ β) = .inl (π ⬝ x) :=
  rfl

omit [DecidableEq 𝔸] in
@[simp]
theorem Sum.perm_inr {α β : Type*} [HasPerm 𝔸 α] [HasPerm 𝔸 β] (π : Finperm 𝔸) (x : β) :
    (π ⬝ .inr x : α ⊕ β) = .inr (π ⬝ x) :=
  rfl

instance {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] : MulPerm 𝔸 (α ⊕ β) where
  one_perm x := by
    cases x <;> simp only [Sum.perm_inl, Sum.perm_inr, one_perm]
  mul_perm π₁ π₂ x := by
    cases x <;> simp only [Sum.perm_inl, Sum.perm_inr, mul_perm]

theorem Sum.inl_equivariant {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    Equivariant 𝔸 (Sum.inl : α → α ⊕ β) := by
  simp only [Function.equivariant_iff, perm_inl, implies_true]

theorem Sum.inr_equivariant {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    Equivariant 𝔸 (Sum.inr : β → α ⊕ β) := by
  simp only [Function.equivariant_iff, perm_inr, implies_true]

instance {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β] : Nominal 𝔸 (α ⊕ β) where
  supported := by
    rintro (x | x)
    · exact (Nominal.supported x).map Sum.inl Sum.inl_equivariant
    · exact (Nominal.supported x).map Sum.inr Sum.inr_equivariant

/-- This proves that `α ⊕ β` is the coproduct of `α` and `β` in the category of nominal sets. -/
def Sum.elim_equivariant {α β γ : Type*}
    [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    (f : α → γ) (g : β → γ) (hf : Equivariant 𝔸 f) (hg : Equivariant 𝔸 g) :
    Equivariant 𝔸 (Sum.elim f g) := by
  rw [Function.equivariant_iff]
  rintro π (x | x)
  · rw [elim_inl, perm_inl, apply_perm_eq hf, elim_inl]
  · rw [elim_inr, perm_inr, apply_perm_eq hg, elim_inr]

@[simp]
theorem Sum.supp_inl {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β] (x : α) :
    supp 𝔸 (Sum.inl x : α ⊕ β) = supp 𝔸 x :=
  supp_apply_eq_of_injective (Sum.inl : α → α ⊕ β) Sum.inl_injective Sum.inl_equivariant x

@[simp]
theorem Sum.supp_inr {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β] (x : β) :
    supp 𝔸 (Sum.inr x : α ⊕ β) = supp 𝔸 x :=
  supp_apply_eq_of_injective (Sum.inr : β → α ⊕ β) Sum.inr_injective Sum.inr_equivariant x

/-!
# Binary products
-/

instance {α β : Type*} [HasPerm 𝔸 α] [HasPerm 𝔸 β] : HasPerm 𝔸 (α × β) where
  perm π x := (π ⬝ x.1, π ⬝ x.2)

omit [DecidableEq 𝔸] in
theorem Prod.perm_def {α β : Type*} [HasPerm 𝔸 α] [HasPerm 𝔸 β] (π : Finperm 𝔸) (x : α × β) :
    π ⬝ x = (π ⬝ x.1, π ⬝ x.2) :=
  rfl

omit [DecidableEq 𝔸] in
@[simp]
theorem Prod.perm_mk {α β : Type*} [HasPerm 𝔸 α] [HasPerm 𝔸 β] (π : Finperm 𝔸) (x : α) (y : β) :
    π ⬝ (x, y) = (π ⬝ x, π ⬝ y) :=
  rfl

instance {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] : MulPerm 𝔸 (α × β) where
  one_perm x := by rw [Prod.perm_def, one_perm, one_perm]
  mul_perm π₁ π₂ x := by rw [Prod.perm_def, mul_perm, mul_perm]; rfl

theorem Prod.fst_equivariant {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    Equivariant 𝔸 (Prod.fst : α × β → α) := by
  simp only [Function.equivariant_iff, Prod.forall, perm_mk, implies_true]

theorem Prod.snd_equivariant {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    Equivariant 𝔸 (Prod.snd : α × β → β) := by
  simp only [Function.equivariant_iff, Prod.forall, perm_mk, implies_true]

theorem Supports.pair {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    {s t : Finset 𝔸} {x : α} {y : β}
    (hs : Supports s x) (ht : Supports t y) :
    Supports (s ∪ t) (x, y) := by
  intro π hπ
  aesop

theorem FinitelySupported.pair {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    {x : α} {y : β} (hx : FinitelySupported 𝔸 x) (hy : FinitelySupported 𝔸 y) :
    FinitelySupported 𝔸 (x, y) := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hy
  exact ⟨s ∪ t, hs.pair ht⟩

instance {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β] : Nominal 𝔸 (α × β) where
  supported x := (Nominal.supported x.1).pair (Nominal.supported x.2)

/-- This proves that `α × β` is the product of `α` and `β` in the category of nominal sets. -/
theorem Prod.pair_equivariant {α β γ : Type*}
    [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    (f : γ → α) (g : γ → β) (hf : Equivariant 𝔸 f) (hg : Equivariant 𝔸 g) :
    Equivariant 𝔸 (λ x ↦ (f x, g x)) := by
  rw [Function.equivariant_iff]
  intro π x
  rw [perm_mk, apply_perm_eq hf, apply_perm_eq hg]

@[simp]
theorem Prod.supp_mk [Infinite 𝔸] {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β] (x : α) (y : β) :
    supp 𝔸 (x, y) = supp 𝔸 x ∪ supp 𝔸 y := by
  apply subset_antisymm
  · apply supp_minimal
    apply Supports.pair
    · exact Nominal.supp_supports 𝔸 x
    · exact Nominal.supp_supports 𝔸 y
  · apply Finset.union_subset
    · exact supp_apply_subset fst fst_equivariant (x, y)
    · exact supp_apply_subset snd snd_equivariant (x, y)

@[simp]
theorem Prod.fresh_iff [Infinite 𝔸] {α β γ : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (x : α) (y : β) (z : γ) :
    z #[𝔸] (x, y) ↔ z #[𝔸] x ∧ z #[𝔸] y := by
  rw [fresh_def, fresh_def, fresh_def, supp_mk, Finset.disjoint_union_right]

theorem Equivariant.uncurry {α β : Type*} {γ : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    {f : α → β → γ} (h : Equivariant 𝔸 f) : Equivariant 𝔸 (Function.uncurry f) := by
  simp only [Function.equivariant_iff, funext_iff, Function.perm_def, Prod.forall,
    Function.uncurry_apply_pair, Prod.perm_mk] at h ⊢
  intro π x y
  rw [← h π x (π ⬝ y), inv_perm_perm]

theorem Equivariant.uncurry₂ {α β γ : Type*} {δ : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    [MulPerm 𝔸 γ] [MulPerm 𝔸 δ] {f : α → β → γ → δ} (h : Equivariant 𝔸 f) :
    Equivariant 𝔸 (λ x (y : β × γ) ↦ f x y.1 y.2) := by
  simp only [Function.equivariant_iff, funext_iff, Function.perm_def, Prod.forall,
    Function.uncurry_apply_pair, Prod.perm_mk] at h ⊢
  intro π x y z
  rw [← h π x y z]

/-!
# Equalisers
-/

def Nominal.Equaliser {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    (f g : α → β) (_hf : Equivariant 𝔸 f) (_hg : Equivariant 𝔸 g) :=
  {x : α // f x = g x}

namespace Nominal.Equaliser

variable {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    {f g : α → β} {hf : Equivariant 𝔸 f} {hg : Equivariant 𝔸 g}

protected def val (x : Equaliser f g hf hg) : α :=
  Subtype.val x

attribute [coe] Equaliser.val

instance : CoeOut (Equaliser f g hf hg) α where
  coe := Equaliser.val

protected theorem prop (x : Equaliser f g hf hg) :
    f (x : α) = g (x : α) :=
  Subtype.prop x

@[ext]
protected theorem ext {x y : Equaliser f g hf hg} (h : (x : α) = y) : x = y :=
  Subtype.ext h

theorem val_injective :
    Function.Injective (Equaliser.val : Equaliser f g hf hg → α) :=
  Subtype.val_injective

instance : HasPerm 𝔸 (Equaliser f g hf hg) where
  perm π x := ⟨π ⬝ (x : α), by rw [← apply_perm_eq hf, ← apply_perm_eq hg, x.prop]⟩

@[simp]
theorem perm_coe (π : Finperm 𝔸) (x : Equaliser f g hf hg) :
    ((π ⬝ x : Equaliser f g hf hg) : α) = π ⬝ (x : α) :=
  rfl

instance : MulPerm 𝔸 (Equaliser f g hf hg) where
  one_perm _ := by
    ext
    rw [perm_coe, one_perm]
  mul_perm _ _ _ := by
    ext
    rw [perm_coe, perm_coe, perm_coe, mul_perm]

instance {α β : Type*} [Nominal 𝔸 α] [MulPerm 𝔸 β]
    {f g : α → β} {hf : Equivariant 𝔸 f} {hg : Equivariant 𝔸 g}
    [Infinite 𝔸] : Nominal 𝔸 (Equaliser f g hf hg) where
  supported x := by
    use supp 𝔸 (x : α)
    intro π hπ
    ext
    exact supp_supports 𝔸 (x : α) π hπ

theorem val_equivariant : Equivariant 𝔸 (Equaliser.val : Equaliser f g hf hg → α) := by
  simp only [Function.equivariant_iff, perm_coe, implies_true]

def factor (f g : α → β) (hf : Equivariant 𝔸 f) (hg : Equivariant 𝔸 g)
    {γ : Type*} [MulPerm 𝔸 γ] (h : γ → α) (hfh : ∀ x, f (h x) = g (h x))
    (x : γ) : Equaliser f g hf hg :=
  ⟨h x, hfh x⟩

theorem factor_equivariant {f g : α → β} {hf : Equivariant 𝔸 f} {hg : Equivariant 𝔸 g}
    {γ : Type*} [MulPerm 𝔸 γ] {h : γ → α} {hfh : ∀ x, f (h x) = g (h x)}
    (hh : Equivariant 𝔸 h) :
    Equivariant 𝔸 (factor f g hf hg h hfh) := by
  rw [Function.equivariant_iff]
  intro π hπ
  ext
  exact apply_perm_eq hh π hπ

end Nominal.Equaliser

/-!
# Initial and terminal object
-/

instance {α : Type*} [Subsingleton α] : MulPerm 𝔸 α where
  perm _ := id
  one_perm _ := rfl
  mul_perm _ _ _ := rfl

instance {α : Type*} [Subsingleton α] : Nominal 𝔸 α where
  supported _ := ⟨∅, λ _ _ ↦ rfl⟩

theorem equivariant_of_isEmpty {α β : Type*} [IsEmpty α] [MulPerm 𝔸 β] (f : α → β) :
    Equivariant 𝔸 f := by
  intro π
  ext x
  cases IsEmpty.false x

theorem equivariant_of_subsingleton {α β : Type*} [MulPerm 𝔸 α] [Subsingleton β] (f : α → β) :
    Equivariant 𝔸 f := by
  intro π
  ext x
  apply Subsingleton.allEq

/-!
# Coreflection

We show that the category of nominal sets is coreflective in the category of `Finperm 𝔸`-sets.
-/

/-- A finitely supported element of `α`. -/
def FS (𝔸 : Type*) [DecidableEq 𝔸] (α : Type*) [MulPerm 𝔸 α] :=
  {x : α // FinitelySupported 𝔸 x}

def FS.val {α : Type*} [MulPerm 𝔸 α] (x : FS 𝔸 α) : α :=
  Subtype.val x

attribute [coe] FS.val

instance {α : Type*} [MulPerm 𝔸 α] : CoeOut (FS 𝔸 α) α where
  coe := FS.val

theorem FS.prop {α : Type*} [MulPerm 𝔸 α] (x : FS 𝔸 α) : FinitelySupported 𝔸 (x : α) :=
  Subtype.prop x

@[ext]
theorem FS.ext {α : Type*} [MulPerm 𝔸 α] {x y : FS 𝔸 α} (h : (x : α) = y) : x = y :=
  Subtype.ext h

theorem FS.val_injective {α : Type*} [MulPerm 𝔸 α] :
    Function.Injective (FS.val : FS 𝔸 α → α) :=
  Subtype.val_injective

instance {α : Type*} [MulPerm 𝔸 α] : HasPerm 𝔸 (FS 𝔸 α) where
  perm π x := ⟨π ⬝ (x : α), x.prop.perm π⟩

@[simp]
theorem FS.perm_coe {α : Type*} [MulPerm 𝔸 α] (x : FS 𝔸 α) (π : Finperm 𝔸) :
    ((π ⬝ x : FS 𝔸 α) : α) = π ⬝ x :=
  rfl

instance {α : Type*} [MulPerm 𝔸 α] : MulPerm 𝔸 (FS 𝔸 α) where
  one_perm _ := FS.ext (by rw [FS.perm_coe, one_perm])
  mul_perm _ _ _ := FS.ext (by simp only [FS.perm_coe, mul_perm])

theorem FS.val_equivariant {α : Type*} [MulPerm 𝔸 α] :
    Equivariant 𝔸 (FS.val (𝔸 := 𝔸) (α := α)) := by
  rw [Function.equivariant_iff]
  intro π x
  rfl

instance {α : Type*} [MulPerm 𝔸 α] : Nominal 𝔸 (FS 𝔸 α) where
  supported x := x.prop.of_map FS.val_injective FS.val_equivariant

@[simp]
theorem FS.supports_iff {α : Type*} [MulPerm 𝔸 α] (x : FS 𝔸 α) (s : Finset 𝔸) :
    Supports s x ↔ Supports s (x : α) :=
  ⟨λ h ↦ h.map val val_equivariant, λ h ↦ h.of_map val_injective val_equivariant⟩

/-- The factorisation of an equivariant function from a nominal set through the finitely supported
elements of its codomain. -/
def Equivariant.toFS {α β : Type*} [Nominal 𝔸 α] [MulPerm 𝔸 β]
    {f : α → β} (hf : Equivariant 𝔸 f) (x : α) : FS 𝔸 β :=
  ⟨f x, (Nominal.supported x).map f hf⟩

@[simp]
theorem FS.supp_eq {α : Type*} [MulPerm 𝔸 α] (x : FS 𝔸 α) :
    supp 𝔸 x = supp 𝔸 x.val := by
  ext a
  simp only [Nominal.mem_supp_iff, supports_iff, mem_supp_iff' _ x.prop]

@[simp]
theorem FS.fresh_iff {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : FS 𝔸 α) (y : β) :
    y #[𝔸] x ↔ y #[𝔸] x.val := by
  rw [fresh_def, fresh_def, supp_eq]

/-!
# Function types

As the `perm` instance we want to define is incompatible with the usual one, we use a structure.
We will never put a `Nominal` instance on a general `Π` type.
However, we can put various instances on relation types, because this doesn't conflict with
`Pi.perm` (we don't define a `Nominal` instance for `Prop`).
-/

structure FinpermMap (α β : Type*) where
  protected toFun : α → β

infixr:25 " →ᶠᵖ " => FinpermMap

instance FinpermMap.funLike {α β : Type*} : FunLike (α →ᶠᵖ β) α β where
  coe := FinpermMap.toFun
  coe_injective' f g h := by cases f; congr

@[ext]
theorem ext {α β : Type*} {f g : α →ᶠᵖ β} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  rw [FinpermMap.mk.injEq]
  ext x
  exact h x

@[simp]
theorem FinpermMap.mk_apply {α β : Type*} (f : α → β) (x : α) :
    (⟨f⟩ : α →ᶠᵖ β) x = f x :=
  rfl

instance {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    HasPerm 𝔸 (α →ᶠᵖ β) where
  perm π f := ⟨λ x ↦ π ⬝ f (π⁻¹ ⬝ x)⟩

@[simp]
theorem FinpermMap.perm_def {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    (f : α →ᶠᵖ β) (x : α) (π : Finperm 𝔸) :
    (π ⬝ f) x = π ⬝ f (π⁻¹ ⬝ x) :=
  rfl

@[simp]
theorem FinpermMap.perm_apply_perm {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    (f : α →ᶠᵖ β) (x : α) (π : Finperm 𝔸) :
    (π ⬝ f) (π ⬝ x) = π ⬝ f x := by
  rw [perm_def, inv_perm_perm]

theorem FinpermMap.perm_eq_iff {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    (f : α →ᶠᵖ β) (π : Finperm 𝔸) :
    π ⬝ f = f ↔ ∀ x, π ⬝ f x = f (π ⬝ x) := by
  constructor
  · intro h x
    rw [← perm_apply_perm, h]
  · intro h
    apply DFunLike.ext
    intro x
    rw [perm_def, h, perm_inv_perm]

instance {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    MulPerm 𝔸 (FinpermMap α β) where
  one_perm _ := by
    apply DFunLike.ext
    simp only [FinpermMap.perm_def, inv_one, one_perm, implies_true]
  mul_perm _ _ _ := by
    apply DFunLike.ext
    simp only [FinpermMap.perm_def, mul_inv_rev, mul_perm, implies_true]

theorem FinpermMap.supports_iff {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    (f : FinpermMap α β) (s : Finset 𝔸) :
    Supports s f ↔
    ∀ π : Finperm 𝔸, (∀ a ∈ s, π a = a) → ∀ x, π ⬝ f x = f (π ⬝ x) := by
  simp_rw [← perm_eq_iff]
  rfl

theorem FinitelySupported.graph {α β : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] {f : α → β}
    (h : FinitelySupported 𝔸 f) :
    FinitelySupported 𝔸 (λ x y ↦ f x = y) := by
  simp only [Function.finitelySupported_iff, funext_iff, Function.perm_def, IsDiscrete.perm_eq,
    eq_iff_iff] at h ⊢
  obtain ⟨s, hs⟩ := h
  use s
  intro π hπ x y
  rw [← hs π hπ, perm_eq_iff_eq_inv_perm]

/-!
# Finitely supported functions
-/

/-- A finitely supported map from `α` to `β`. -/
structure NominalMap (𝔸 α β : Type*) [DecidableEq 𝔸]
    [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    extends α →ᶠᵖ β where
  supported' : FinitelySupported 𝔸 toFinpermMap

notation:25 α " →ₙ[" 𝔸:25 "] " β:0 => NominalMap 𝔸 α β

instance NominalMap.funLike {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    FunLike (α →ₙ[𝔸] β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    congr
    apply DFunLike.coe_injective
    exact h
