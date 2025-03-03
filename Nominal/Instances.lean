import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Logic.Function.Coequalizer
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

@[simp]
theorem IsDiscrete.supp_eq {α : Sort*} [MulPerm 𝔸 α] [IsDiscrete 𝔸 α] (x : α) :
    supp 𝔸 x = ∅ := by
  rw [← Finset.subset_empty]
  apply supp_minimal
  intro _ _
  rw [perm_eq]

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

theorem Equivariant.empty_supports {α : Type*} [MulPerm 𝔸 α] (x : α) (h : Equivariant 𝔸 x) :
    Supports (∅ : Finset 𝔸) x := by
  intro π hπ
  rw [h]

theorem Equivariant.supp_eq_empty {α : Type*} [MulPerm 𝔸 α] {x : α}
    (h : Equivariant 𝔸 x) :
    supp 𝔸 x = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro a ha
  rw [mem_supp_iff' _ ⟨∅, h.empty_supports⟩] at ha
  have := ha ∅ (λ π _ ↦ h π)
  cases this

theorem equivariant_iff_supp_eq_empty [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (x : α) :
    Equivariant 𝔸 x ↔ supp 𝔸 x = ∅ := by
  constructor
  · exact Equivariant.supp_eq_empty
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
# Equivariant subtype
-/

/-- An equivariant element of `α`. -/
structure EQ (𝔸 : Type*) [DecidableEq 𝔸] (α : Type*) [HasPerm 𝔸 α] where
  val : α
  equivariant : Equivariant 𝔸 val

attribute [coe] EQ.val

instance {α : Type*} [HasPerm 𝔸 α] : CoeOut (EQ 𝔸 α) α where
  coe := EQ.val

@[ext]
theorem EQ.ext {α : Type*} [HasPerm 𝔸 α] {x y : EQ 𝔸 α}
    (h : (x : α) = y) : x = y := by
  cases x; cases h; rfl

theorem EQ.val_injective {α : Type*} [HasPerm 𝔸 α] :
    Function.Injective (EQ.val : EQ 𝔸 α → α) := by
  intro x y h
  cases x
  cases h
  rfl

@[simp]
theorem EQ.val_mk {α : Type*} [HasPerm 𝔸 α] {x : α} {h : Equivariant 𝔸 x} :
    ((⟨x, h⟩ : EQ 𝔸 α) : α) = x :=
  rfl

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

@[simp]
theorem FS.val_mk {α : Type*} [MulPerm 𝔸 α] {x : α} {h : FinitelySupported 𝔸 x} :
    ((⟨x, h⟩ : FS 𝔸 α) : α) = x :=
  rfl

@[simp]
theorem FS.val_mk' {α : Type*} [MulPerm 𝔸 α] {x : α} {h : FinitelySupported 𝔸 x} :
    FS.val (⟨x, h⟩ : {x : α // FinitelySupported 𝔸 x}) = x :=
  rfl

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

theorem Equivariant.toFS_equivariant {α β : Type*} [Nominal 𝔸 α] [MulPerm 𝔸 β]
    {f : α → β} (hf : Equivariant 𝔸 f) :
    Equivariant 𝔸 hf.toFS := by
  intro π
  ext x : 2
  rw [Function.perm_def, Equivariant.toFS, FS.perm_coe, FS.val_mk', apply_perm_eq hf, perm_inv_perm]
  rfl

@[simp]
protected theorem FS.supp_eq {α : Type*} [MulPerm 𝔸 α] (x : FS 𝔸 α) :
    supp 𝔸 x = supp 𝔸 x.val := by
  ext a
  simp only [Nominal.mem_supp_iff, supports_iff, mem_supp_iff' _ x.prop]

@[simp]
theorem FS.fresh_iff {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : FS 𝔸 α) (y : β) :
    y #[𝔸] x ↔ y #[𝔸] x.val := by
  rw [fresh_def, fresh_def, FS.supp_eq]

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
# Initial and terminal object
-/

instance : MulPerm 𝔸 Unit where
  perm _ := id
  one_perm _ := rfl
  mul_perm _ _ _ := rfl

instance : Nominal 𝔸 Unit where
  supported _ := ⟨∅, λ _ _ ↦ rfl⟩

instance : MulPerm 𝔸 PUnit where
  perm _ := id
  one_perm _ := rfl
  mul_perm _ _ _ := rfl

instance : Nominal 𝔸 PUnit where
  supported _ := ⟨∅, λ _ _ ↦ rfl⟩

instance : MulPerm 𝔸 Empty where
  perm _ := id
  one_perm _ := rfl
  mul_perm _ _ _ := rfl

instance : Nominal 𝔸 Empty where
  supported _ := ⟨∅, λ _ _ ↦ rfl⟩

instance : MulPerm 𝔸 PEmpty where
  perm _ := id
  one_perm _ := rfl
  mul_perm _ _ _ := rfl

instance : Nominal 𝔸 PEmpty where
  supported _ := ⟨∅, λ _ _ ↦ rfl⟩

/-!
# Sigma types
-/

instance {ι : Type*} {α : ι → Type*} [(i : ι) → HasPerm 𝔸 (α i)] : HasPerm 𝔸 ((i : ι) × α i) where
  perm π x := x.map id (λ _ ↦ (π ⬝ ·))

omit [DecidableEq 𝔸] in
theorem Sigma.perm_def {ι : Type*} {α : ι → Type*} [(i : ι) → HasPerm 𝔸 (α i)]
    (π : Finperm 𝔸) (x : (i : ι) × α i) :
    π ⬝ x = x.map id (λ _ ↦ (π ⬝ ·)) :=
  rfl

omit [DecidableEq 𝔸] in
@[simp]
theorem Sigma.perm_mk {ι : Type*} {α : ι → Type*} [(i : ι) → HasPerm 𝔸 (α i)]
    (π : Finperm 𝔸) {i : ι} (x : α i) :
    π ⬝ (⟨i, x⟩ : (i : ι) × α i) = ⟨i, π ⬝ x⟩ :=
  rfl

omit [DecidableEq 𝔸] in
@[simp]
theorem Sigma.perm_fst {ι : Type*} {α : ι → Type*} [(i : ι) → HasPerm 𝔸 (α i)]
    (π : Finperm 𝔸) (x : (i : ι) × α i) :
    (π ⬝ x).fst = x.fst :=
  rfl

omit [DecidableEq 𝔸] in
@[simp]
theorem Sigma.perm_snd {ι : Type*} {α : ι → Type*} [(i : ι) → HasPerm 𝔸 (α i)]
    (π : Finperm 𝔸) (x : (i : ι) × α i) :
    (π ⬝ x).snd = π ⬝ x.snd :=
  rfl

instance {ι : Type*} {α : ι → Type*} [(i : ι) → MulPerm 𝔸 (α i)] : MulPerm 𝔸 ((i : ι) × α i) where
  one_perm := by
    rintro ⟨i, x⟩
    rw [Sigma.perm_mk, one_perm]
  mul_perm := by
    rintro π₁ π₂ ⟨i, x⟩
    rw [Sigma.perm_mk, mul_perm]
    rfl

theorem Sigma.mk_equivariant {ι : Type*} {α : ι → Type*} [(i : ι) → MulPerm 𝔸 (α i)] (i : ι) :
    Equivariant 𝔸 (mk i : α i → (j : ι) × α j) := by
  intro π
  ext x : 1
  rw [Function.perm_def, perm_mk, perm_inv_perm]

/-- Note that we can't directly say that `snd` is equivariant, as it is a dependent type. -/
theorem Sigma.supports_snd {ι : Type*} {α : ι → Type*}
    [(i : ι) → MulPerm 𝔸 (α i)] {s : Finset 𝔸} {x : (i : ι) × α i}
    (h : Supports s x) :
    Supports s x.snd := by
  intro π hπ
  rw [← perm_snd]
  congr 1
  exact h π hπ

theorem Sigma.snd_finitelySupported {ι : Type*} {α : ι → Type*}
    [(i : ι) → MulPerm 𝔸 (α i)] {x : (i : ι) × α i}
    (h : FinitelySupported 𝔸 x) :
    FinitelySupported 𝔸 x.snd := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, supports_snd hs⟩

theorem Sigma.supports_mk {ι : Type*} {α : ι → Type*} [(i : ι) → MulPerm 𝔸 (α i)]
    {i : ι} {x : α i} {s : Finset 𝔸} (hs : Supports s x) :
    Supports s (⟨i, x⟩ : (i : ι) × α i) :=
  hs.map _ (mk_equivariant i)

instance [Infinite 𝔸] {ι : Type*} {α : ι → Type*} [(i : ι) → Nominal 𝔸 (α i)] :
    Nominal 𝔸 ((i : ι) × α i) where
  supported := by
    rintro ⟨i, x⟩
    exact ⟨_, Sigma.supports_mk (Nominal.supp_supports 𝔸 x)⟩

/-!
# Product types
-/

/-- The pointwise product of nominal sets.
This is, in general, not a nominal set. -/
@[ext]
structure PointProduct (𝔸 : Type*) [DecidableEq 𝔸]
    {ι : Type*} (α : ι → Type*) [(i : ι) → HasPerm 𝔸 (α i)] where
  pr i : α i

instance {ι : Type*} {α : ι → Type*} [(i : ι) → HasPerm 𝔸 (α i)] :
    HasPerm 𝔸 (PointProduct 𝔸 α) where
  perm π x := ⟨λ i ↦ π ⬝ x.pr i⟩

theorem PointProduct.perm_def {ι : Type*} {α : ι → Type*} [(i : ι) → HasPerm 𝔸 (α i)]
    (x : PointProduct 𝔸 α) (π : Finperm 𝔸) :
    π ⬝ x = ⟨λ i ↦ π ⬝ x.pr i⟩ :=
  rfl

@[simp]
theorem PointProduct.perm_pr {ι : Type*} {α : ι → Type*} [(i : ι) → HasPerm 𝔸 (α i)]
    (x : PointProduct 𝔸 α) (π : Finperm 𝔸) (i : ι) :
    (π ⬝ x).pr i = π ⬝ x.pr i :=
  rfl

instance {ι : Type*} {α : ι → Type*} [(i : ι) → MulPerm 𝔸 (α i)] :
    MulPerm 𝔸 (PointProduct 𝔸 α) where
  one_perm x := PointProduct.ext (funext (λ i ↦ one_perm (x.pr i)))
  mul_perm π₁ π₂ x := PointProduct.ext (funext (λ i ↦ mul_perm π₁ π₂ (x.pr i)))

/-- The categorical product of nominal sets. -/
def Product (𝔸 : Type*) [DecidableEq 𝔸]
    {ι : Type*} (α : ι → Type*) [(i : ι) → MulPerm 𝔸 (α i)] :=
  FS 𝔸 (PointProduct 𝔸 α)

instance {ι : Type*} {α : ι → Type*} [(i : ι) → MulPerm 𝔸 (α i)] :
    Nominal 𝔸 (Product 𝔸 α) :=
  inferInstanceAs (Nominal 𝔸 (FS 𝔸 (PointProduct 𝔸 α)))

def Product.pr {ι : Type*} {α : ι → Type*} [(i : ι) → MulPerm 𝔸 (α i)]
    (i : ι) (x : Product 𝔸 α) : α i :=
  x.val.pr i

theorem Product.pr_equivariant {ι : Type*} {α : ι → Type*} [(i : ι) → MulPerm 𝔸 (α i)]
    (i : ι) : Equivariant 𝔸 (pr i : Product 𝔸 α → α i) := by
  intro π
  ext x
  rw [Function.perm_def, perm_eq_iff_eq_inv_perm]
  rfl

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
# Coequalisers
-/

def Nominal.Coequaliser {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    (f g : α → β) (_hf : Equivariant 𝔸 f) (_hg : Equivariant 𝔸 g) :=
  Function.Coequalizer f g

namespace Nominal.Coequaliser

variable {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
  {f g : α → β} {hf : Equivariant 𝔸 f} {hg : Equivariant 𝔸 g}

protected def mk (x : β) : Coequaliser f g hf hg :=
  Function.Coequalizer.mk f g x

theorem condition (x : α) : (.mk (f x) : Coequaliser f g hf hg) = .mk (g x) :=
  Function.Coequalizer.condition _ _ x

theorem mk_surjective : Function.Surjective (.mk : β → Coequaliser f g hf hg) :=
  Function.Coequalizer.mk_surjective f g

instance : HasPerm 𝔸 (Coequaliser f g hf hg) where
  perm π := Function.Coequalizer.desc f g (λ x ↦ .mk (π ⬝ x))
    (by
      ext x
      simp only [Function.comp_apply, apply_perm_eq hf, apply_perm_eq hg]
      exact Function.Coequalizer.condition _ _ _)

@[simp]
theorem perm_mk (π : Finperm 𝔸) (x : β) :
    π ⬝ (.mk x : Coequaliser f g hf hg) = .mk (π ⬝ x) :=
  rfl

instance : MulPerm 𝔸 (Coequaliser f g hf hg) where
  one_perm x := by
    obtain ⟨x, rfl⟩ := mk_surjective x
    rw [perm_mk, one_perm]
  mul_perm π₁ π₂ x := by
    obtain ⟨x, rfl⟩ := mk_surjective x
    rw [perm_mk, mul_perm]
    rfl

theorem mk_equivariant : Equivariant 𝔸 (.mk : β → Coequaliser f g hf hg) := by
  intro π
  ext x
  simp only [Function.perm_def, perm_mk, perm_inv_perm]

instance {α β : Type*} [MulPerm 𝔸 α] [Nominal 𝔸 β]
    {f g : α → β} {hf : Equivariant 𝔸 f} {hg : Equivariant 𝔸 g}
    [Infinite 𝔸] : Nominal 𝔸 (Coequaliser f g hf hg) where
  supported x := by
    obtain ⟨x, rfl⟩ := mk_surjective x
    exact ⟨_, (Nominal.supp_supports 𝔸 x).map _ mk_equivariant⟩

def factor (f g : α → β) (hf : Equivariant 𝔸 f) (hg : Equivariant 𝔸 g)
    {γ : Type*} [MulPerm 𝔸 γ] (h : β → γ) (hfh : ∀ x, h (f x) = h (g x)) :
    Coequaliser f g hf hg → γ :=
  Function.Coequalizer.desc f g h (funext hfh)

theorem factor_equivariant {f g : α → β} {hf : Equivariant 𝔸 f} {hg : Equivariant 𝔸 g}
    {γ : Type*} [MulPerm 𝔸 γ] {h : β → γ} {hfh : ∀ x, h (f x) = h (g x)}
    (hh : Equivariant 𝔸 h) :
    Equivariant 𝔸 (factor f g hf hg h hfh) := by
  intro π
  ext x
  obtain ⟨x, rfl⟩ := mk_surjective x
  rw [Function.perm_def, factor, perm_mk, Coequaliser.mk, Coequaliser.mk,
    Function.Coequalizer.desc_mk, Function.Coequalizer.desc_mk, apply_perm_eq hh, perm_inv_perm]

end Nominal.Coequaliser

/-!
# Finite permutations
-/

instance : HasPerm 𝔸 (Finperm 𝔸) where
  perm π π' := π * π' * π⁻¹

theorem Finperm.perm_def (π π' : Finperm 𝔸) :
    π ⬝ π' = π * π' * π⁻¹ :=
  rfl

instance : MulPerm 𝔸 (Finperm 𝔸) where
  one_perm π := by rw [Finperm.perm_def, one_mul, inv_one, mul_one]
  mul_perm π₁ π₂ π := by simp only [perm_def, mul_assoc, mul_inv_rev]

theorem Finperm.support_supports (π : Finperm 𝔸) :
    Supports π.support π := by
  intro π' ha
  ext a
  simp only [perm_def, coe_mul, Function.comp_apply]
  by_cases ha' : π'⁻¹ a ∈ π.support
  · have := ha (π'⁻¹ a) ha'
    rw [apply_inv_self] at this
    rw [← this]
    by_cases ha'' : π a ∈ π.support
    · rw [ha (π a) ha'']
    · rw [mem_support_iff, not_not, EmbeddingLike.apply_eq_iff_eq] at ha''
      rw [ha'']
      conv_lhs => rw [this, apply_inv_self]
  · rw [mem_support_iff, not_not] at ha'
    rw [ha', apply_inv_self]
    by_cases ha'' : a ∈ π.support
    · have := ha a ha''
      rw [eq_comm, ← inv_apply_eq_iff_eq] at this
      rw [this] at ha'
      rw [ha']
    · rw [mem_support_iff, not_not] at ha''
      rw [ha'']

theorem Finperm.support_subset_of_supports [Infinite 𝔸] {π : Finperm 𝔸} {s : Finset 𝔸}
    (hs : Supports s π) :
    π.support ⊆ s := by
  intro a ha
  by_contra ha'
  obtain ⟨b, hb⟩ := Infinite.exists_not_mem_finset (π.support ∪ s)
  rw [Finset.mem_union, not_or] at hb
  have := hs (swap a b) ?_
  · suffices a = b by cases this; tauto
    rw [mem_support_iff, not_not] at hb
    have := congr_arg (· (π⁻¹ b)) this
    simp only [perm_def, swap_inv, coe_mul, Function.comp_apply, apply_inv_self] at this
    rw [eq_comm, ← inv_apply_eq_iff_eq] at hb
    rw [mem_support_iff] at ha
    rw [hb.1, swap_apply_right, swap_apply_of_ne_of_ne ha] at this
    · rw [inv_apply_eq_iff_eq] at hb
      rwa [hb.1, EmbeddingLike.apply_eq_iff_eq] at this
    · rintro rfl
      rw [inv_apply_self] at hb
      rw [← hb.1] at ha
      contradiction
  · intro c hc
    rw [swap_apply_of_ne_of_ne]
    · rintro rfl; contradiction
    · rintro rfl; tauto

instance : Nominal 𝔸 (Finperm 𝔸) where
  supported π := ⟨π.support, π.support_supports⟩

@[simp]
protected theorem Finperm.supp_eq [Infinite 𝔸] (π : Finperm 𝔸) :
    supp 𝔸 π = π.support := by
  apply subset_antisymm
  · apply supp_minimal
    exact π.support_supports
  · apply support_subset_of_supports
    apply Nominal.supp_supports

theorem Finperm.fresh_iff [Infinite 𝔸] (π : Finperm 𝔸) {α : Type*} [MulPerm 𝔸 α] (x : α) :
    π #[𝔸] x ↔ ∀ a ∈ supp 𝔸 x, π a = a := by
  simp only [fresh_def, Finperm.supp_eq, Finset.disjoint_iff_inter_eq_empty,
    Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter, mem_support_iff, ne_eq, not_and,
    not_imp_not]

theorem perm_eq_of_fresh [Infinite 𝔸] {π : Finperm 𝔸} {α : Type*} [Nominal 𝔸 α] {x : α}
    (h : π #[𝔸] x) :
    π ⬝ x = x := by
  apply Nominal.supp_supports 𝔸
  rwa [Finperm.fresh_iff] at h

theorem inv_perm_eq_of_fresh [Infinite 𝔸] {π : Finperm 𝔸} {α : Type*} [Nominal 𝔸 α] {x : α}
    (h : π #[𝔸] x) :
    π⁻¹ ⬝ x = x := by
  conv_lhs => rw [← perm_eq_of_fresh h, inv_perm_perm]

/-!
# Sets

We define instances on `Set α` that agree definitionally with those on `α → Prop`.
-/

instance {α : Type*} [HasPerm 𝔸 α] :
    HasPerm 𝔸 (Set α) where
  perm π s := {x | π⁻¹ ⬝ x ∈ s}

@[simp]
theorem Set.perm_def {α : Type*} [HasPerm 𝔸 α] (π : Finperm 𝔸) (s : Set α) :
    π ⬝ s = {x | π⁻¹ ⬝ x ∈ s} :=
  rfl

instance {α : Type*} [MulPerm 𝔸 α] :
    MulPerm 𝔸 (Set α) where
  one_perm := one_perm (α := α → Prop)
  mul_perm := mul_perm (α := α → Prop)
