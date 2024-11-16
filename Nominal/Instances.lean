import Mathlib.Algebra.Group.Action.Sum
import Nominal.Equivariant

open MulAction Finperm

variable {𝔸 : Type*} [DecidableEq 𝔸]

/-!
# Sets
-/
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

theorem Set.finitelySupported_of_finite [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (s : Set α) (hs : s.Finite) :
    FinitelySupported 𝔸 s := by
  lift s to Finset α using hs
  rw [Finset.coe_finitelySupported_iff]
  apply Nominal.supported

theorem FinitelySupported.compl {α : Type*} [MulAction (Finperm 𝔸) α]
    {s : Set α} (hs : FinitelySupported 𝔸 s) :
    FinitelySupported 𝔸 sᶜ := by
  obtain ⟨t, ht⟩ := hs
  refine ⟨t, ?_⟩
  intro π hπ
  rw [Set.smul_set_compl, ht π hπ]

end Set

/-!
# Discrete structures
-/

set_option linter.unusedVariables false in
/-- A type alias to endow a type `α` with its discrete nominal structure. -/
def Discrete (𝔸 : Type*) (α : Type*) :=
  α

instance {α : Type*} : MulAction (Finperm 𝔸) (Discrete 𝔸 α) where
  smul _ := id
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance {α : Type*} : Nominal 𝔸 (Discrete 𝔸 α) where
  supported _ := ⟨∅, λ _ _ ↦ rfl⟩

/-- Typeclass for discrete nominal structures. -/
class IsDiscrete (𝔸 : Type*) [DecidableEq 𝔸] (α : Type*) [MulAction (Finperm 𝔸) α] : Prop where
  smul_eq : ∀ π : Finperm 𝔸, ∀ x : α, π • x = x

attribute [simp] IsDiscrete.smul_eq

instance {α : Type*} : IsDiscrete 𝔸 (Discrete 𝔸 α) where
  smul_eq _ _ := rfl

theorem equivariant_of_discrete {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (f : Discrete 𝔸 α → Discrete 𝔸 β) :
    Equivariant 𝔸 f :=
  λ _ _ ↦ rfl

/--
An object is called a *global section* if it is fixed under all permutations of names.
-/
def IsGlobalSection (𝔸 : Type*) {α : Type*} [DecidableEq 𝔸] [MulAction (Finperm 𝔸) α] (x : α) :=
  ∀ π : Finperm 𝔸, π • x = x

theorem isGlobalSection_of_isDiscrete (𝔸 : Type*) [DecidableEq 𝔸]
    {α : Type*} [MulAction (Finperm 𝔸) α] [IsDiscrete 𝔸 α] (x : α) :
    IsGlobalSection 𝔸 x := by
  simp [IsGlobalSection]

theorem isGlobalSection_iff_supp_eq_empty [Infinite 𝔸] {α : Type*} [Nominal 𝔸 α] (x : α) :
    IsGlobalSection 𝔸 x ↔ supp 𝔸 x = ∅ := by
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

theorem IsGlobalSection.map {α : Type*} [MulAction (Finperm 𝔸) α] {x : α} (h : IsGlobalSection 𝔸 x)
    {β : Type*} [MulAction (Finperm 𝔸) β]
    {f : α → β} (hf : Equivariant 𝔸 f) :
    IsGlobalSection 𝔸 (f x) := by
  intro π
  rw [hf, h]

theorem Equivariant.apply_isGlobalSection_of_isDiscrete
    {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β] [IsDiscrete 𝔸 α]
    {f : α → β} (hf : Equivariant 𝔸 f) (x : α) :
    IsGlobalSection 𝔸 (f x) :=
  (isGlobalSection_of_isDiscrete 𝔸 x).map hf

/-- One part of the adjunction between the discrete and global sections functors. -/
def liftDiscrete {α β : Type*} [MulAction (Finperm 𝔸) β] (f : α → β)
    (_hf : ∀ x, IsGlobalSection 𝔸 (f x)) :
    Discrete 𝔸 α → β :=
  f

theorem liftDiscrete_equivariant {α β : Type*} [MulAction (Finperm 𝔸) β] (f : α → β)
    (hf : ∀ x, IsGlobalSection 𝔸 (f x)) :
    Equivariant 𝔸 (liftDiscrete f hf) := by
  intro π x
  rw [IsDiscrete.smul_eq π x, liftDiscrete, hf]

/-!
# Binary coproducts
-/

theorem Sum.inl_equivariant {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β] :
    Equivariant 𝔸 (Sum.inl : α → α ⊕ β) :=
  λ _ _ ↦ rfl

theorem Sum.inr_equivariant {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β] :
    Equivariant 𝔸 (Sum.inr : β → α ⊕ β) :=
  λ _ _ ↦ rfl

instance {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β] : Nominal 𝔸 (α ⊕ β) where
  supported := by
    rintro (x | x)
    · exact (Nominal.supported x).map Sum.inl Sum.inl_equivariant
    · exact (Nominal.supported x).map Sum.inr Sum.inr_equivariant

/-- This proves that `α ⊕ β` is the coproduct of `α` and `β` in the category of nominal sets. -/
def Sum.elim_equivariant {α β γ : Type*}
    [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β] [MulAction (Finperm 𝔸) γ]
    (f : α → γ) (g : β → γ) (hf : Equivariant 𝔸 f) (hg : Equivariant 𝔸 g) :
    Equivariant 𝔸 (Sum.elim f g) := by
  rintro π (x | x)
  · rw [elim_inl, smul_inl, hf, elim_inl]
  · rw [elim_inr, smul_inr, hg, elim_inr]

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

theorem Prod.fst_equivariant {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β] :
    Equivariant 𝔸 (Prod.fst : α × β → α) :=
  λ _ _ ↦ rfl

theorem Prod.snd_equivariant {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β] :
    Equivariant 𝔸 (Prod.snd : α × β → β) :=
  λ _ _ ↦ rfl

theorem MulAction.Supports.pair {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    {s t : Finset 𝔸} {x : α} {y : β}
    (hs : Supports (Finperm 𝔸) (s : Set 𝔸) x) (ht : Supports (Finperm 𝔸) (t : Set 𝔸) y) :
    Supports (Finperm 𝔸) ((s ∪ t : Finset 𝔸) : Set 𝔸) (x, y) := by
  intro π hπ
  aesop

theorem FinitelySupported.pair {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    {x : α} {y : β} (hx : FinitelySupported 𝔸 x) (hy : FinitelySupported 𝔸 y) :
    FinitelySupported 𝔸 (x, y) := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hy
  exact ⟨s ∪ t, hs.pair ht⟩

instance {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β] : Nominal 𝔸 (α × β) where
  supported x := (Nominal.supported x.1).pair (Nominal.supported x.2)

/-- This proves that `α × β` is the product of `α` and `β` in the category of nominal sets. -/
theorem Prod.pair_equivariant {α β γ : Type*}
    [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β] [MulAction (Finperm 𝔸) γ]
    (f : γ → α) (g : γ → β) (hf : Equivariant 𝔸 f) (hg : Equivariant 𝔸 g) :
    Equivariant 𝔸 (λ x ↦ (f x, g x)) := by
  intro π x
  rw [smul_mk, hf, hg]

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

/-!
# Initial and terminal object
-/

instance {α : Type*} [Subsingleton α] : MulAction (Finperm 𝔸) α where
  smul _ := id
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance {α : Type*} [Subsingleton α] : Nominal 𝔸 α where
  supported _ := ⟨∅, λ _ _ ↦ rfl⟩

instance {α : Type*} [Subsingleton α] : IsDiscrete 𝔸 α where
  smul_eq _ _ := rfl

theorem equivariant_of_isEmpty {α β : Type*} [IsEmpty α] [MulAction (Finperm 𝔸) β] (f : α → β) :
    Equivariant 𝔸 f := by
  intro π x
  cases IsEmpty.false x

theorem equivariant_of_subsingleton {α β : Type*} [MulAction (Finperm 𝔸) α] [Subsingleton β] (f : α → β) :
    Equivariant 𝔸 f := by
  intro π x
  apply Subsingleton.allEq

/-!
# Coreflection

We show that the category of nominal sets is coreflective in the category of `Finperm 𝔸`-sets.
-/

/-- A finitely supported element of `α`. -/
def FS (𝔸 : Type*) [DecidableEq 𝔸] (α : Type*) [MulAction (Finperm 𝔸) α] :=
  {x : α // FinitelySupported 𝔸 x}

def FS.val {α : Type*} [MulAction (Finperm 𝔸) α] (x : FS 𝔸 α) : α :=
  Subtype.val x

attribute [coe] FS.val

instance {α : Type*} [MulAction (Finperm 𝔸) α] : CoeOut (FS 𝔸 α) α where
  coe := FS.val

@[ext]
theorem FS.ext {α : Type*} [MulAction (Finperm 𝔸) α] {x y : FS 𝔸 α} (h : (x : α) = y) : x = y :=
  Subtype.ext h

theorem FS.val_injective {α : Type*} [MulAction (Finperm 𝔸) α] :
    Function.Injective (FS.val : FS 𝔸 α → α) :=
  Subtype.val_injective

instance {α : Type*} [MulAction (Finperm 𝔸) α] : SMul (Finperm 𝔸) (FS 𝔸 α) where
  smul π x := ⟨π • (x : α), x.prop.smul π⟩

@[simp]
theorem FS.smul_coe {α : Type*} [MulAction (Finperm 𝔸) α] (x : FS 𝔸 α) (π : Finperm 𝔸) :
    ((π • x : FS 𝔸 α) : α) = π • x :=
  rfl

instance {α : Type*} [MulAction (Finperm 𝔸) α] : MulAction (Finperm 𝔸) (FS 𝔸 α) where
  one_smul _ := FS.ext (by rw [FS.smul_coe, one_smul])
  mul_smul _ _ _ := FS.ext (by simp only [FS.smul_coe, mul_smul])

theorem FS.val_equivariant {α : Type*} [MulAction (Finperm 𝔸) α] :
    Equivariant 𝔸 (FS.val (𝔸 := 𝔸) (α := α)) :=
  λ _ _ ↦ rfl

instance {α : Type*} [MulAction (Finperm 𝔸) α] : Nominal 𝔸 (FS 𝔸 α) where
  supported x := x.prop.of_map FS.val_injective FS.val_equivariant

@[simp]
theorem FS.supports_iff {α : Type*} [MulAction (Finperm 𝔸) α] (x : FS 𝔸 α) (s : Finset 𝔸) :
    Supports (Finperm 𝔸) (s : Set 𝔸) x ↔ Supports (Finperm 𝔸) (s : Set 𝔸) (x : α) :=
  ⟨λ h ↦ h.map val val_equivariant, λ h ↦ h.of_map val_injective val_equivariant⟩

/-- The factorisation of an equivariant function from a nominal set through the finitely supported
elements of its codomain. -/
def Equivariant.toFS {α β : Type*} [Nominal 𝔸 α] [MulAction (Finperm 𝔸) β]
    {f : α → β} (hf : Equivariant 𝔸 f) (x : α) : FS 𝔸 β :=
  ⟨f x, (Nominal.supported x).map f hf⟩

/-!
# Function types

As the `SMul` instance we want to define is incompatible with the usual one, we use a structure.
-/

structure FinpermMap (α β : Type*) where
  protected toFun : α → β

infixr:25 " →ᶠᵖ " => FinpermMap

instance FinpermMap.funLike {α β : Type*} : FunLike (α →ᶠᵖ β) α β where
  coe := FinpermMap.toFun
  coe_injective' f g h := by cases f; congr

instance {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β] :
    SMul (Finperm 𝔸) (α →ᶠᵖ β) where
  smul π f := ⟨λ x ↦ π • f (π⁻¹ • x)⟩

theorem FinpermMap.smul_def {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (f : α →ᶠᵖ β) (x : α) (π : Finperm 𝔸) :
    (π • f) x = π • f (π⁻¹ • x) :=
  rfl

@[simp]
theorem FinpermMap.smul_apply_smul {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (f : α →ᶠᵖ β) (x : α) (π : Finperm 𝔸) :
    (π • f) (π • x) = π • f x := by
  rw [smul_def, inv_smul_smul]

theorem FinpermMap.smul_eq_iff {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (f : α →ᶠᵖ β) (π : Finperm 𝔸) :
    π • f = f ↔ ∀ x, π • f x = f (π • x) := by
  constructor
  · intro h x
    rw [← smul_apply_smul, h]
  · intro h
    apply DFunLike.ext
    intro x
    rw [smul_def, h, smul_inv_smul]

instance {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β] :
    MulAction (Finperm 𝔸) (FinpermMap α β) where
  one_smul _ := by
    apply DFunLike.ext
    simp only [FinpermMap.smul_def, inv_one, one_smul, implies_true]
  mul_smul _ _ _ := by
    apply DFunLike.ext
    simp only [FinpermMap.smul_def, mul_inv_rev, mul_smul, implies_true]

theorem FinpermMap.supports_iff {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (f : FinpermMap α β) (s : Finset 𝔸) :
    Supports (Finperm 𝔸) (s : Set 𝔸) f ↔
    ∀ π : Finperm 𝔸, (∀ a ∈ s, π a = a) → ∀ x, π • f x = f (π • x) := by
  simp_rw [← smul_eq_iff]
  rfl

/-!
# Finitely supported functions
-/

/-- A finitely supported map from `α` to `β`. -/
structure NominalMap (𝔸 α β : Type*) [DecidableEq 𝔸]
    [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    extends α →ᶠᵖ β where
  supported' : FinitelySupported 𝔸 toFinpermMap

notation:25 α " →ₙ[" 𝔸:25 "] " β:0 => NominalMap 𝔸 α β
