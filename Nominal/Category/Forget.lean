import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Subobject.WellPowered
import Nominal.Category.Coreflection
import Nominal.Category.ForgetAdjoints
import Nominal.Category.Limits

open CategoryTheory Functor Limits

variable {𝔸 : Type*} [DecidableEq 𝔸]

/-- The forgetful functor from nominal sets to `Type _` has a right adjoint.
In particular, it preserves all colimits. -/
def Nominal.forgetAdj (𝔸 : Type*) [DecidableEq 𝔸] :
    forget (Bundled (Nominal 𝔸)) ⊣ MulPerm.power 𝔸 ⋙ nominalCoreflection 𝔸 :=
  (nominalInclusionAdj 𝔸).comp (MulPerm.powerAdj 𝔸)

instance Nominal.forget_preservesColimits.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    PreservesColimitsOfSize (forget (Bundled.{max u v} (Nominal 𝔸))) :=
  (Nominal.forgetAdj 𝔸).leftAdjoint_preservesColimits

def Nominal.forget_pairCone_isLimit.{v} (K : Discrete WalkingPair ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit ((forget (Bundled.{v} (Nominal 𝔸))).mapCone (pairCone K)) where
  lift s x := ⟨s.π.app ⟨.left⟩ x, s.π.app ⟨.right⟩ x⟩
  fac s j := by
    obtain ⟨j | j⟩ := j
    case left => rfl
    case right => rfl
  uniq s m h := by
    ext x
    apply Prod.ext
    · exact congr_arg (· x) (h ⟨.left⟩)
    · exact congr_arg (· x) (h ⟨.right⟩)

instance Nominal.forget_preservesBinaryProducts.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] :
    PreservesLimitsOfShape (Discrete WalkingPair) (forget (Bundled.{v} (Nominal 𝔸))) :=
  ⟨λ {K} ↦ preservesLimit_of_preserves_limit_cone
    (Nominal.pairCone_isLimit K) (Nominal.forget_pairCone_isLimit K)⟩

def Nominal.forget_emptyCone_isLimit.{v} (K : Discrete PEmpty ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit ((forget (Bundled.{v} (Nominal 𝔸))).mapCone (emptyCone K)) where
  lift s _ := PUnit.unit

instance Nominal.forget_preservesEmpty.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] :
    PreservesLimitsOfShape (Discrete PEmpty) (forget (Bundled.{v} (Nominal 𝔸))) :=
  ⟨λ {K} ↦ preservesLimit_of_preserves_limit_cone
    (Nominal.emptyCone_isLimit K) (Nominal.forget_emptyCone_isLimit K)⟩

instance Nominal.forget_preservesFiniteProducts.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    PreservesFiniteProducts.{v} (forget (Bundled.{v} (Nominal 𝔸))) :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

def Nominal.forget_equaliserCone_isLimit.{v} [Infinite 𝔸]
    (K : WalkingParallelPair ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit ((forget (Bundled.{v} (Nominal 𝔸))).mapCone (equaliserCone K)) where
  lift s x :=
    ⟨s.π.app .zero x, congr_arg (· x) ((s.π.naturality .left).symm.trans (s.π.naturality .right))⟩
  fac s j := by
    cases j
    case zero => rfl
    case one => exact s.w .left
  uniq s m h := by
    ext x
    have := congr_arg (· x) (h .zero)
    exact Equaliser.val_injective
      (hf := (K.map .left).equivariant) (hg := (K.map .right).equivariant) this

instance Nominal.forget_preservesEqualisers.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    PreservesLimitsOfShape WalkingParallelPair (forget (Bundled.{v} (Nominal 𝔸))) :=
  ⟨λ {K} ↦ preservesLimit_of_preserves_limit_cone
    (Nominal.equaliserCone_isLimit K) (Nominal.forget_equaliserCone_isLimit K)⟩

instance Nominal.forget_preservesFiniteLimits.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    PreservesFiniteLimits.{v} (forget (Bundled (Nominal 𝔸))) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

theorem Nominal.mono_iff_injective [Infinite 𝔸] {α β : Bundled (Nominal 𝔸)} (f : α ⟶ β) :
    Mono f ↔ Function.Injective f :=
  ConcreteCategory.mono_iff_injective_of_preservesPullback f

theorem Nominal.epi_iff_surjective.{u, v}
    {𝔸 : Type u} [DecidableEq 𝔸] [Infinite 𝔸] {α β : Bundled.{max u v} (Nominal 𝔸)} (f : α ⟶ β) :
    Epi f ↔ Function.Surjective f :=
  ConcreteCategory.epi_iff_surjective_of_preservesPushout f

theorem Set.range_equivariant {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    Equivariant 𝔸 (Set.range : (α → β) → Set β) := by
  intro π
  ext f x
  simp only [Function.perm_def, perm_def, mem_range, inv_inv, perm_left_cancel_iff, mem_setOf_eq]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨π ⬝ y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨π⁻¹ ⬝ y, congr_arg f (perm_inv_perm π y)⟩

instance {α : Type*} [HasPerm 𝔸 α] (s : EQ 𝔸 (Set α)) :
    HasPerm 𝔸 s where
  perm π x := ⟨π ⬝ x, by
    have := congr_arg (x.val ∈ ·) (s.equivariant π⁻¹)
    simp only [Subtype.coe_prop, eq_iff_iff, iff_true] at this
    exact this⟩

@[simp]
theorem EQ.coe_perm {α : Type*} [HasPerm 𝔸 α] (s : EQ 𝔸 (Set α)) (x : s.val) (π : Finperm 𝔸) :
    ((π ⬝ x : s.val) : α) = π ⬝ x :=
  rfl

instance (𝔸 : Type*) [DecidableEq 𝔸] {α : Type*} [MulPerm 𝔸 α] (s : EQ 𝔸 (Set α)) :
    MulPerm 𝔸 s where
  one_perm x := by ext; rw [EQ.coe_perm, one_perm]
  mul_perm π₁ π₂ x := by ext; rw [EQ.coe_perm, mul_perm]; rfl

instance (𝔸 : Type*) [DecidableEq 𝔸] {α : Type*} [Nominal 𝔸 α] (s : EQ 𝔸 (Set α)) :
    Nominal 𝔸 s where
  supported x := by
    obtain ⟨s, hs⟩ := Nominal.supported (𝔸 := 𝔸) x.val
    use s
    intro π h
    ext
    exact hs π h

theorem EQ.val_equivariant {α : Type*} [MulPerm 𝔸 α] (s : EQ 𝔸 (Set α)) :
    Equivariant 𝔸 (Subtype.val : s.val → α) := by
  intro π
  ext x
  simp only [Function.perm_def, coe_perm, perm_inv_perm]

def subobjectToSubset [Infinite 𝔸] {α : Bundled (Nominal 𝔸)} : Subobject α → EQ 𝔸 (Set α) :=
  Subobject.lift (λ β f _ ↦ ⟨Set.range f, f.equivariant.map Set.range_equivariant⟩) <| by
    rintro β γ f g hf hg e rfl
    ext x
    simp only [Nominal.forget_hom, Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.hom y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e.inv y, congr_arg (λ x ↦ g (x y)) e.inv_hom_id⟩

def subsetToSubobject [Infinite 𝔸] {α : Bundled (Nominal 𝔸)} (s : EQ 𝔸 (Set α)) : Subobject α :=
  haveI : Mono (show ⟨s.val, inferInstance⟩ ⟶ α from ⟨Subtype.val, EQ.val_equivariant s⟩) :=
    (Nominal.mono_iff_injective _).mpr (by exact Subtype.val_injective)
  Subobject.mk (show ⟨s.val, inferInstance⟩ ⟶ α from ⟨Subtype.val, EQ.val_equivariant s⟩)

def Nominal.subobjectEquiv [Infinite 𝔸]
    (α : Bundled (Nominal 𝔸)) : Subobject α ≃ EQ 𝔸 (Set α) where
  toFun := subobjectToSubset
  invFun := subsetToSubobject
  left_inv := by
    apply Subobject.ind
    intro β f hf
    haveI : Mono (show ⟨(subobjectToSubset (Subobject.mk f)).val, inferInstance⟩ ⟶ α from
        ⟨Subtype.val, EQ.val_equivariant (subobjectToSubset (Subobject.mk f))⟩) :=
      (mono_iff_injective _).mpr (by exact Subtype.val_injective)
    rw [mono_iff_injective] at hf
    refine Subobject.mk_eq_mk_of_comm _ _ ?_ ?_
    · refine ⟨⟨(Equiv.ofInjective f hf).symm, ?_⟩, ⟨Equiv.ofInjective f hf, ?_⟩, ?_, ?_⟩
      · intro π
        ext x
        apply hf
        apply (apply_perm_eq f.equivariant π ((Equiv.ofInjective f hf).symm (π⁻¹ ⬝ x))).symm.trans
        rw [Equiv.apply_ofInjective_symm hf]
        change π ⬝ f _ = x
        rw [Equiv.apply_ofInjective_symm hf]
        exact perm_inv_perm _ _
      · intro π
        ext x
        change π ⬝ f (π⁻¹ ⬝ x) = f x
        rw [perm_eq_iff_eq_inv_perm]
        exact (apply_perm_eq f.equivariant π⁻¹ x).symm
      · ext x
        exact congr_arg Subtype.val ((Equiv.ofInjective f hf).right_inv x)
      · ext x
        exact (Equiv.ofInjective f hf).left_inv x
    · ext x
      exact congr_arg Subtype.val ((Equiv.ofInjective f hf).right_inv x)
  right_inv := by
    intro s
    simp only [subobjectToSubset, forget_hom, subsetToSubobject, Subobject.lift_mk, EQ.mk_coe,
      Subtype.range_coe_subtype, Set.setOf_mem_eq]

instance Nominal.wellPowered.{v} [Infinite 𝔸] : WellPowered.{v} (Bundled.{v} (Nominal 𝔸)) where
  subobject_small α := ⟨_, ⟨Nominal.subobjectEquiv α⟩⟩
