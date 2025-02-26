import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Nominal.Instances

/-!
# The category of nominal sets

In this file, we translate our nominal definitions into the language of mathlib's
category theory library. This allows us to appeal to results such as the adjoint
functor theorem.

It is difficult to use these results directly because they are stated in bundled form
(objects are types-with-structure not types together with typeclass-inferred structure),
whereas the rest of this nominal sets library uses unbundled form.
-/

open CategoryTheory Functor Limits

variable {𝔸 : Type*} [DecidableEq 𝔸]

protected def MulPerm.of (α : Type*) [str : MulPerm 𝔸 α] : Bundled (MulPerm 𝔸) :=
  ⟨α, str⟩

instance MulPerm.coeSort : CoeSort (Bundled (MulPerm 𝔸)) (Type _) :=
  ⟨Bundled.α⟩

theorem MulPerm.coe_mk (α) (str) : (@Bundled.mk (MulPerm 𝔸) α str : Type _) = α :=
  rfl

instance {α : Bundled (MulPerm 𝔸)} : MulPerm 𝔸 α :=
  α.str

protected def Nominal.of (α : Type*) [str : Nominal 𝔸 α] : Bundled (Nominal 𝔸) :=
  ⟨α, str⟩

instance Nominal.coeSort : CoeSort (Bundled (Nominal 𝔸)) (Type _) :=
  ⟨Bundled.α⟩

theorem Nominal.coe_mk (α) (str) : (@Bundled.mk (Nominal 𝔸) α str : Type _) = α :=
  rfl

instance {α : Bundled (Nominal 𝔸)} : Nominal 𝔸 α :=
  α.str

instance {α β : Type*} [HasPerm 𝔸 α] [HasPerm 𝔸 β] :
    FunLike {f : α → β // Equivariant 𝔸 f} α β where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

instance : Category (Bundled (MulPerm 𝔸)) where
  Hom α β := {f : α → β // Equivariant 𝔸 f}
  id _ := ⟨id, id_equivariant⟩
  comp f g := ⟨g.val ∘ f.val, g.prop.comp f.prop⟩

instance : ConcreteCategory (Bundled (MulPerm 𝔸)) (λ α β ↦ {f : α → β // Equivariant 𝔸 f}) where
  hom := id
  ofHom := id

instance : Category (Bundled (Nominal 𝔸)) where
  Hom α β := {f : α → β // Equivariant 𝔸 f}
  id _ := ⟨id, id_equivariant⟩
  comp f g := ⟨g.val ∘ f.val, g.prop.comp f.prop⟩

instance : ConcreteCategory (Bundled (Nominal 𝔸)) (λ α β ↦ {f : α → β // Equivariant 𝔸 f}) where
  hom := id
  ofHom := id

def nominalInclusion (𝔸 : Type*) [DecidableEq 𝔸] : Bundled (Nominal 𝔸) ⥤ Bundled (MulPerm 𝔸) where
  obj := Bundled.map (λ x ↦ x.toMulPerm)
  map := id

def nominalCoreflection (𝔸 : Type*) [DecidableEq 𝔸] : Bundled (MulPerm 𝔸) ⥤ Bundled (Nominal 𝔸) where
  obj α := Nominal.of (FS 𝔸 α)
  map {X Y} f := ⟨(f.prop.comp FS.val_equivariant).toFS, (f.prop.comp FS.val_equivariant).toFS_equivariant⟩

def nominalInclusionFullyFaithful : FullyFaithful (nominalInclusion 𝔸) where
  preimage := id

instance : Faithful (nominalInclusion 𝔸) := nominalInclusionFullyFaithful.faithful

instance : Full (nominalInclusion 𝔸) := nominalInclusionFullyFaithful.full

def nominalInclusionAdj (𝔸 : Type*) [DecidableEq 𝔸] : nominalInclusion 𝔸 ⊣ nominalCoreflection 𝔸 where
  unit := {
    app α := ⟨id_equivariant.toFS, id_equivariant.toFS_equivariant⟩
  }
  counit := {
    app α := ⟨FS.val, FS.val_equivariant⟩
  }

instance nominalCoreflective : Coreflective (nominalInclusion 𝔸) where
  R := nominalCoreflection 𝔸
  adj := nominalInclusionAdj 𝔸

/-! We can identify the `Finperm 𝔸`-types with functors from the delooping of `Finperm 𝔸` into `Type u`. -/

instance {F : SingleObj (Finperm 𝔸) ⥤ Type*} : MulPerm 𝔸 (F.obj (SingleObj.star (Finperm 𝔸))) where
  perm := F.map
  one_perm x := congr_fun (F.map_id (SingleObj.star (Finperm 𝔸))) x
  mul_perm π₁ π₂ x := congr_fun (F.map_comp π₂ π₁) x

def mulPermMap.{u} (𝔸 : Type*) [DecidableEq 𝔸] : Bundled (MulPerm.{u + 1} 𝔸) ⥤ SingleObj (Finperm 𝔸) ⥤ Type u where
  obj α := {
    obj _ := α
    map π x := π ⬝ x
    map_id _ := by ext; exact one_perm _
    map_comp _ _ := by ext; exact mul_perm _ _ _
  }
  map f := {
    app _ := f
    naturality _ _ π := by ext a; exact (apply_perm_eq f.prop π a).symm
  }

def mulPermMap'.{u} (𝔸 : Type*) [DecidableEq 𝔸] : (SingleObj (Finperm 𝔸) ⥤ Type u) ⥤ Bundled (MulPerm.{u + 1} 𝔸) where
  obj F := MulPerm.of (F.obj (SingleObj.star (Finperm 𝔸)))
  map f := {
    val := f.app (SingleObj.star (Finperm 𝔸))
    property := by
      rw [Function.equivariant_iff]
      intro π x
      exact (congr_fun (f.naturality (X := SingleObj.star _) (Y := SingleObj.star _) π) x).symm
  }

def mulPermEquiv.{u} : Bundled (MulPerm.{u + 1} 𝔸) ≌ (SingleObj (Finperm 𝔸) ⥤ Type u) where
  functor := mulPermMap 𝔸
  inverse := mulPermMap' 𝔸
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-!
# Limits and colimits
-/

/-! We show that the coreflection of nominal sets in `Finperm 𝔸`-sets is a geometric morphism. -/

instance nominalCoreflection_preservesLimits.{u, v} (𝔸 : Type v) [DecidableEq 𝔸] :
    PreservesLimitsOfSize (C := Bundled (MulPerm.{u + 1} 𝔸)) (D := Bundled (Nominal.{u + 1} 𝔸))
      (nominalCoreflection 𝔸) :=
  (nominalInclusionAdj 𝔸).rightAdjoint_preservesLimits

instance Nominal.hasLimits (𝔸 : Type*) [DecidableEq 𝔸] :
    HasLimits (Bundled (Nominal 𝔸)) :=
  sorry

instance nominalInclusion_preservesColimits.{u, v} (𝔸 : Type v) [DecidableEq 𝔸] :
    PreservesColimitsOfSize (C := Bundled (Nominal.{u + 1} 𝔸)) (D := Bundled (MulPerm.{u + 1} 𝔸))
      (nominalInclusion 𝔸) :=
  (nominalInclusionAdj 𝔸).leftAdjoint_preservesColimits

instance nominalInclusion_preservesEqualisers.{u, v} (𝔸 : Type v) [DecidableEq 𝔸] :
    PreservesLimitsOfShape (C := Bundled (Nominal.{u + 1} 𝔸)) (D := Bundled (MulPerm.{u + 1} 𝔸))
      WalkingParallelPair (nominalInclusion 𝔸) :=
  sorry

instance nominalInclusion_preservesFiniteProducts.{u, v} (𝔸 : Type v) [DecidableEq 𝔸] :
    PreservesFiniteProducts (C := Bundled (Nominal.{u + 1} 𝔸)) (D := Bundled (MulPerm.{u + 1} 𝔸))
      (nominalInclusion 𝔸) :=
  sorry

instance nominalInclusion_preservesFiniteLimits.{u, v} (𝔸 : Type v) [DecidableEq 𝔸] :
    PreservesFiniteLimits (C := Bundled (Nominal.{u + 1} 𝔸)) (D := Bundled (MulPerm.{u + 1} 𝔸))
      (nominalInclusion 𝔸) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _
