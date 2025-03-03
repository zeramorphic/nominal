import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.SingleObj
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

instance {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    FunLike (EQ 𝔸 (α → β)) α β where
  coe := EQ.val
  coe_injective' := EQ.val_injective

@[simp]
theorem EQ.mk_coe {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] (f : α → β) (hf : Equivariant 𝔸 f) :
    (EQ.mk f hf : α → β) = f :=
  rfl

instance : Category (Bundled (MulPerm 𝔸)) where
  Hom α β := EQ 𝔸 (α → β)
  id _ := ⟨id, id_equivariant⟩
  comp f g := ⟨g.val ∘ f.val, g.equivariant.comp f.equivariant⟩

instance : ConcreteCategory (Bundled (MulPerm 𝔸)) (λ α β ↦ EQ 𝔸 (α → β)) where
  hom := id
  ofHom := id

@[simp]
theorem MulPerm.forget_hom {α β : Bundled (MulPerm 𝔸)} (f : α ⟶ β) :
    ConcreteCategory.hom f = f :=
  rfl

instance {α : Bundled (MulPerm 𝔸)} : MulPerm 𝔸 ((forget (Bundled (MulPerm 𝔸))).obj α) :=
  α.str

instance : Category (Bundled (Nominal 𝔸)) where
  Hom α β := EQ 𝔸 (α → β)
  id _ := ⟨id, id_equivariant⟩
  comp f g := ⟨g.val ∘ f.val, g.equivariant.comp f.equivariant⟩

instance : ConcreteCategory (Bundled (Nominal 𝔸)) (λ α β ↦ EQ 𝔸 (α → β)) where
  hom := id
  ofHom := id

@[simp]
theorem Nominal.forget_hom {α β : Bundled (Nominal 𝔸)} (f : α ⟶ β) :
    ConcreteCategory.hom f = f :=
  rfl

instance {α : Bundled (Nominal 𝔸)} : Nominal 𝔸 ((forget (Bundled (Nominal 𝔸))).obj α) :=
  α.str

/-! We can identify the `Finperm 𝔸`-types with functors from
the delooping of `Finperm 𝔸` into `Type u`. -/

instance {F : SingleObj (Finperm 𝔸) ⥤ Type*} :
    MulPerm 𝔸 (F.obj (SingleObj.star (Finperm 𝔸))) where
  perm := F.map
  one_perm x := congr_fun (F.map_id (SingleObj.star (Finperm 𝔸))) x
  mul_perm π₁ π₂ x := congr_fun (F.map_comp π₂ π₁) x

def mulPermMap.{u} (𝔸 : Type*) [DecidableEq 𝔸] :
    Bundled (MulPerm.{u + 1} 𝔸) ⥤ SingleObj (Finperm 𝔸) ⥤ Type u where
  obj α := {
    obj _ := α
    map π x := π ⬝ x
    map_id _ := by ext; exact one_perm _
    map_comp _ _ := by ext; exact mul_perm _ _ _
  }
  map f := {
    app _ := f
    naturality _ _ π := by ext a; exact (apply_perm_eq f.equivariant π a).symm
  }

def mulPermMap'.{u} (𝔸 : Type*) [DecidableEq 𝔸] :
    (SingleObj (Finperm 𝔸) ⥤ Type u) ⥤ Bundled (MulPerm.{u + 1} 𝔸) where
  obj F := MulPerm.of (F.obj (SingleObj.star (Finperm 𝔸)))
  map f := {
    val := f.app (SingleObj.star (Finperm 𝔸))
    equivariant := by
      rw [Function.equivariant_iff]
      intro π x
      exact (congr_fun (f.naturality (X := SingleObj.star _) (Y := SingleObj.star _) π) x).symm
  }

def mulPermEquiv.{u} (𝔸 : Type*) [DecidableEq 𝔸] :
    Bundled (MulPerm.{u + 1} 𝔸) ≌ SingleObj (Finperm 𝔸) ⥤ Type u where
  functor := mulPermMap 𝔸
  inverse := mulPermMap' 𝔸
  unitIso := Iso.refl _
  counitIso := Iso.refl _

noncomputable instance mulPermEquiv_createsLimits (𝔸 : Type*) [DecidableEq 𝔸] :
    CreatesLimits (mulPermEquiv 𝔸).functor :=
  createsLimitsOfIsEquivalence _

noncomputable instance mulPermEquiv_inverse_preservesLimits (𝔸 : Type*) [DecidableEq 𝔸] :
    CreatesLimits (mulPermEquiv 𝔸).inverse :=
  createsLimitsOfIsEquivalence _

noncomputable instance mulPermEquiv_createsColimits (𝔸 : Type*) [DecidableEq 𝔸] :
    CreatesColimits (mulPermEquiv 𝔸).functor :=
  createsColimitsOfIsEquivalence _

noncomputable instance mulPermEquiv_inverse_createsColimits (𝔸 : Type*) [DecidableEq 𝔸] :
    CreatesColimits (mulPermEquiv 𝔸).inverse :=
  createsColimitsOfIsEquivalence _

instance MulPerm.hasLimits.{v₁, u₁, v} (𝔸 : Type*) [DecidableEq 𝔸] [UnivLE.{u₁, v}] :
    HasLimitsOfSize.{v₁, u₁} (Bundled.{v} (MulPerm 𝔸)) :=
  hasLimits_of_hasLimits_createsLimits (mulPermEquiv 𝔸).functor

instance MulPerm.hasColimits.{v₁, u₁, v} (𝔸 : Type*) [DecidableEq 𝔸] [UnivLE.{u₁, v}] :
    HasColimitsOfSize.{v₁, u₁} (Bundled.{v} (MulPerm 𝔸)) :=
  hasColimits_of_hasColimits_createsColimits (mulPermEquiv 𝔸).functor

def Nominal.discrete.{u} (𝔸 : Type*) [DecidableEq 𝔸] :
    Type u ⥤ Bundled.{u} (Nominal 𝔸) where
  obj α := Nominal.of (Discrete 𝔸 α)
  map {X Y} f := ⟨f, λ _ ↦ rfl⟩

def discreteFullyFaithful : FullyFaithful (Nominal.discrete 𝔸) where
  preimage f := f.val

instance : Faithful (Nominal.discrete 𝔸) := discreteFullyFaithful.faithful

instance : Full (Nominal.discrete 𝔸) := discreteFullyFaithful.full
