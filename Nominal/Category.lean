import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Whiskering
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

def nominalInclusion.{u} (𝔸 : Type*) [DecidableEq 𝔸] :
    Bundled.{u} (Nominal 𝔸) ⥤ Bundled.{u} (MulPerm 𝔸) where
  obj := Bundled.map (λ x ↦ x.toMulPerm)
  map := id

def nominalCoreflection.{u} (𝔸 : Type*) [DecidableEq 𝔸] :
    Bundled.{u} (MulPerm 𝔸) ⥤ Bundled.{u} (Nominal 𝔸) where
  obj α := Nominal.of (FS 𝔸 α)
  map {X Y} f := ⟨(f.prop.comp FS.val_equivariant).toFS,
    (f.prop.comp FS.val_equivariant).toFS_equivariant⟩

def nominalInclusionFullyFaithful : FullyFaithful (nominalInclusion 𝔸) where
  preimage := id

instance : Faithful (nominalInclusion 𝔸) := nominalInclusionFullyFaithful.faithful

instance : Full (nominalInclusion 𝔸) := nominalInclusionFullyFaithful.full

def nominalInclusionAdj (𝔸 : Type*) [DecidableEq 𝔸] :
    nominalInclusion 𝔸 ⊣ nominalCoreflection 𝔸 where
  unit := {
    app α := ⟨id_equivariant.toFS, id_equivariant.toFS_equivariant⟩
  }
  counit := {
    app α := ⟨FS.val, FS.val_equivariant⟩
  }

instance nominalCoreflective : Coreflective (nominalInclusion 𝔸) where
  R := nominalCoreflection 𝔸
  adj := nominalInclusionAdj 𝔸

def nominalInclusion_nominalCoreflection.{v} (𝔸 : Type*) [DecidableEq 𝔸] :
    nominalInclusion.{v} 𝔸 ⋙ nominalCoreflection 𝔸 ≅ 𝟭 (Bundled (Nominal 𝔸)) where
  hom := {
    app α := ⟨FS.val, FS.val_equivariant⟩
  }
  inv := {
    app α := ⟨λ x ↦ ⟨x, Nominal.supported x⟩, by
      intro π
      ext x
      apply FS.val_injective
      exact perm_inv_perm π x⟩
  }

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
    naturality _ _ π := by ext a; exact (apply_perm_eq f.prop π a).symm
  }

def mulPermMap'.{u} (𝔸 : Type*) [DecidableEq 𝔸] :
    (SingleObj (Finperm 𝔸) ⥤ Type u) ⥤ Bundled (MulPerm.{u + 1} 𝔸) where
  obj F := MulPerm.of (F.obj (SingleObj.star (Finperm 𝔸)))
  map f := {
    val := f.app (SingleObj.star (Finperm 𝔸))
    property := by
      rw [Function.equivariant_iff]
      intro π x
      exact (congr_fun (f.naturality (X := SingleObj.star _) (Y := SingleObj.star _) π) x).symm
  }

def mulPermEquiv.{u} (𝔸 : Type*) [DecidableEq 𝔸] :
    Bundled (MulPerm.{u + 1} 𝔸) ≌ (SingleObj (Finperm 𝔸) ⥤ Type u) where
  functor := mulPermMap 𝔸
  inverse := mulPermMap' 𝔸
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-!
# Limits and colimits
-/

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

/-! We show that the coreflection of nominal sets in `Finperm 𝔸`-sets is a geometric morphism. -/

instance nominalCoreflection_preservesLimits.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] :
    PreservesLimitsOfSize (nominalCoreflection.{v} 𝔸) :=
  (nominalInclusionAdj 𝔸).rightAdjoint_preservesLimits

instance nominalInclusion_preservesColimits.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] :
    PreservesColimitsOfSize (nominalInclusion.{v} 𝔸) :=
  (nominalInclusionAdj 𝔸).leftAdjoint_preservesColimits

def MulPerm.coproductCocone {J : Type*} (K : Discrete J ⥤ Bundled (MulPerm 𝔸)) :
    Cocone K where
  pt := ⟨(j : Discrete J) × K.obj j, inferInstance⟩
  ι := {
    app j := show {f // Equivariant 𝔸 f} from ⟨λ x ↦ ⟨j, x⟩,
      by intro π; ext x; rw [Function.perm_def, Sigma.perm_mk, perm_inv_perm]⟩
    naturality j k h := by cases Discrete.ext (Discrete.eq_of_hom h); simp
  }

def MulPerm.coproductCocone_isColimit {J : Type*} (K : Discrete J ⥤ Bundled (MulPerm 𝔸)) :
    IsColimit (coproductCocone K) where
  desc s := ⟨λ x ↦ s.ι.app x.fst x.snd, by
    intro π
    ext x
    apply (apply_perm_eq (s.ι.app (π⁻¹ ⬝ x).fst).prop π (π⁻¹ ⬝ x).snd).trans
    rw [Sigma.perm_snd, perm_inv_perm]
    rfl⟩
  uniq := by
    intro s m h
    ext x
    exact congr_arg (· x.snd) (h x.fst)

def MulPerm.nominalCoreflection_coproductCocone_isColimit
    {J : Type*} (K : Discrete J ⥤ Bundled (MulPerm 𝔸)) :
    IsColimit ((nominalCoreflection 𝔸).mapCocone (coproductCocone K)) where
  desc s := ⟨λ x ↦ s.ι.app x.val.fst ⟨x.val.snd, Sigma.snd_finitelySupported x.prop⟩, by
    intro π
    ext x
    apply (apply_perm_eq (s.ι.app (π⁻¹ ⬝ x).val.fst).prop π _).trans
    apply congr_arg (s.ι.app _)
    exact perm_inv_perm π (show FS 𝔸 _ from ⟨x.val.snd, Sigma.snd_finitelySupported x.prop⟩)⟩
  uniq := by
    intro s m h
    ext x
    simp only [mapCocone_pt, ConcreteCategory.hom, id_eq, comp_obj, const_obj_obj]
    rw [← h x.val.fst]
    rfl

/-- The coreflector preserves coproducts, but it does not preserve coequalisers.
Hence, it has no right adjoint. -/
instance nominalCoreflection_preservesCoproducts.{u, v} (𝔸 : Type u) [DecidableEq 𝔸]
    {J : Type v} :
    PreservesColimitsOfShape (Discrete J) (nominalCoreflection.{v} 𝔸) := by
  refine ⟨λ {K} ↦ ?_⟩
  apply preservesColimit_of_preserves_colimit_cocone
  · exact MulPerm.coproductCocone_isColimit K
  · exact MulPerm.nominalCoreflection_coproductCocone_isColimit K

def Nominal.coproductCocone [Infinite 𝔸] {J : Type*} (K : Discrete J ⥤ Bundled (Nominal 𝔸)) :
    Cocone K where
  pt := ⟨(j : Discrete J) × K.obj j, inferInstance⟩
  ι := {
    app j := show {f // Equivariant 𝔸 f} from ⟨λ x ↦ ⟨j, x⟩,
      by intro π; ext x; rw [Function.perm_def, Sigma.perm_mk, perm_inv_perm]⟩
    naturality j k h := by cases Discrete.ext (Discrete.eq_of_hom h); simp
  }

def Nominal.coproductCocone_isColimit [Infinite 𝔸] {J : Type*}
    (K : Discrete J ⥤ Bundled (Nominal 𝔸)) :
    IsColimit (coproductCocone K) where
  desc s := ⟨λ x ↦ s.ι.app x.fst x.snd, by
    intro π
    ext x
    apply (apply_perm_eq (s.ι.app (π⁻¹ ⬝ x).fst).prop π (π⁻¹ ⬝ x).snd).trans
    rw [Sigma.perm_snd, perm_inv_perm]
    rfl⟩
  uniq := by
    intro s m h
    ext x
    exact congr_arg (· x.snd) (h x.fst)

instance Nominal.hasCoproducts.{v} [Infinite 𝔸] :
    HasCoproducts.{v} (Bundled.{v} (Nominal 𝔸)) :=
  λ _ ↦ ⟨λ K ↦ ⟨Nominal.coproductCocone K, Nominal.coproductCocone_isColimit K⟩⟩

def Nominal.coequaliserCocone [Infinite 𝔸] (K : WalkingParallelPair ⥤ Bundled (Nominal 𝔸)) :
    Cocone K where
  pt := ⟨Coequaliser (K.map .left) (K.map .right) (K.map .left).prop (K.map .right).prop,
    inferInstance⟩
  ι := {
    app j := match j with
      | .zero => ⟨Coequaliser.mk (hf := (K.map .left).prop) (hg := (K.map .right).prop) ∘
          K.map .right,
        Coequaliser.mk_equivariant.comp (K.map .right).prop⟩
      | .one => ⟨Coequaliser.mk (hf := (K.map .left).prop) (hg := (K.map .right).prop),
        Coequaliser.mk_equivariant⟩
    naturality j k h := by
      ext x
      cases h
      case left =>
        simp only [ConcreteCategory.hom, id_eq, const_obj_obj, const_obj_map, Category.comp_id,
          Function.comp_apply]
        apply Coequaliser.condition
      case right => rfl
      case id =>
        simp only [ConcreteCategory.hom, id_eq, const_obj_obj, walkingParallelPairHom_id,
          CategoryTheory.Functor.map_id, Category.id_comp, const_obj_map, Category.comp_id]
  }

def Nominal.coequaliserCocone_isColimit [Infinite 𝔸]
    (K : WalkingParallelPair ⥤ Bundled (Nominal 𝔸)) :
    IsColimit (coequaliserCocone K) where
  desc s := ⟨Coequaliser.factor
    (K.map .left) (K.map .right) (K.map .left).prop (K.map .right).prop
    (s.ι.app _)
    λ x ↦ (congr_arg (· x) (s.ι.naturality .left)).trans
      (congr_arg (· x) (s.ι.naturality .right)).symm,
    Coequaliser.factor_equivariant (s.ι.app .one).prop⟩
  fac s j := by
    ext x
    cases j
    case zero => exact congr_arg (· x) (s.ι.naturality .right)
    case one => rfl
  uniq s m h := by
    ext x
    obtain ⟨x, rfl⟩ := Coequaliser.mk_surjective (hf := (K.map .left).prop) (hg := (K.map .right).prop) x
    exact congr_arg (· x) (h .one)

instance Nominal.hasCoequalisers [Infinite 𝔸] :
    HasCoequalizers (Bundled (Nominal 𝔸)) :=
  ⟨λ F ↦ ⟨Nominal.coequaliserCocone F, Nominal.coequaliserCocone_isColimit F⟩⟩

instance Nominal.hasLimits.{v₁, u₁, u, v} (𝔸 : Type u) [DecidableEq 𝔸] [UnivLE.{u₁, v}] :
    HasLimitsOfSize.{v₁, u₁} (Bundled.{v} (Nominal 𝔸)) := by
  refine ⟨λ {J} _ ↦ ⟨λ {K} ↦ ?_⟩⟩
  obtain ⟨c, hc⟩ := ((MulPerm.hasLimits.{v₁, u₁} 𝔸).has_limits_of_shape J).has_limit
    (K ⋙ nominalInclusion.{v} 𝔸)
  obtain ⟨hc'⟩ :=
    (nominalCoreflection_preservesLimits 𝔸).preservesLimitsOfShape.preservesLimit.preserves hc
  apply @hasLimitOfIso _ _ _ _ _ _ ⟨_, hc'⟩
  apply (Functor.associator _ _ _).trans
  exact isoWhiskerLeft K (nominalInclusion_nominalCoreflection.{v} 𝔸)

instance Nominal.hasColimits.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    HasColimitsOfSize.{v, v} (Bundled.{v} (Nominal 𝔸)) :=
  has_colimits_of_hasCoequalizers_and_coproducts

def Nominal.pairCone.{v} (K : Discrete WalkingPair ⥤ Bundled.{v} (Nominal 𝔸)) :
    Cone K where
  pt := ⟨K.obj ⟨.left⟩ × K.obj ⟨.right⟩, inferInstance⟩
  π := {
    app j := match j with
      | ⟨.left⟩ => ⟨Prod.fst, Prod.fst_equivariant⟩
      | ⟨.right⟩ => ⟨Prod.snd, Prod.snd_equivariant⟩
    naturality j k f := by
      cases Discrete.ext (Discrete.eq_of_hom f)
      simp only [const_obj_obj, Discrete.functor_map_id, Category.id_comp, Category.comp_id]
  }

def Nominal.pairCone_isLimit (K : Discrete WalkingPair ⥤ Bundled (Nominal 𝔸)) :
    IsLimit (pairCone K) where
  lift s := ⟨λ x ↦ ⟨s.π.app ⟨.left⟩ x, s.π.app ⟨.right⟩ x⟩, by
    intro π
    ext x
    apply Prod.ext
    · apply (apply_perm_eq (s.π.app ⟨.left⟩).prop π _).trans
      rw [perm_inv_perm]
      rfl
    · apply (apply_perm_eq (s.π.app ⟨.right⟩).prop π _).trans
      rw [perm_inv_perm]
      rfl⟩
  fac s j := by
    obtain ⟨j | j⟩ := j
    case left => rfl
    case right => rfl
  uniq s m h := by
    ext x
    apply Prod.ext
    · exact congr_arg (· x) (h ⟨.left⟩)
    · exact congr_arg (· x) (h ⟨.right⟩)

def Nominal.nominalInclusion_pairCone_isLimit (K : Discrete WalkingPair ⥤ Bundled (Nominal 𝔸)) :
    IsLimit ((nominalInclusion 𝔸).mapCone (pairCone K)) where
  lift s := ⟨λ x ↦ ⟨s.π.app ⟨.left⟩ x, s.π.app ⟨.right⟩ x⟩, by
    intro π
    ext x
    apply Prod.ext
    · apply (apply_perm_eq (s.π.app ⟨.left⟩).prop π _).trans
      rw [perm_inv_perm]
      rfl
    · apply (apply_perm_eq (s.π.app ⟨.right⟩).prop π _).trans
      rw [perm_inv_perm]
      rfl⟩
  fac s j := by
    obtain ⟨j | j⟩ := j
    case left => rfl
    case right => rfl
  uniq s m h := by
    ext x
    apply Prod.ext
    · exact congr_arg (· x) (h ⟨.left⟩)
    · exact congr_arg (· x) (h ⟨.right⟩)

instance nominalInclusion_preservesBinaryProducts.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] :
    PreservesLimitsOfShape (Discrete WalkingPair) (nominalInclusion.{v} 𝔸) :=
  ⟨λ {K} ↦ preservesLimit_of_preserves_limit_cone
    (Nominal.pairCone_isLimit K) (Nominal.nominalInclusion_pairCone_isLimit K)⟩

def Nominal.emptyCone.{v} (K : Discrete PEmpty ⥤ Bundled.{v} (Nominal 𝔸)) :
    Cone K where
  pt := ⟨PUnit, inferInstance⟩
  π := {
    app j := j.as.elim
  }

def Nominal.emptyCone_isLimit.{v} (K : Discrete PEmpty ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit (emptyCone K) where
  lift s := ⟨λ _ ↦ PUnit.unit, λ _ ↦ rfl⟩

def Nominal.nominalInclusion_emptyCone_isLimit.{v} (K : Discrete PEmpty ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit ((nominalInclusion 𝔸).mapCone (emptyCone K)) where
  lift s := ⟨λ _ ↦ PUnit.unit, λ _ ↦ rfl⟩

instance nominalInclusion_preservesEmpty.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] :
    PreservesLimitsOfShape (Discrete PEmpty) (nominalInclusion.{v} 𝔸) :=
  ⟨λ {K} ↦ preservesLimit_of_preserves_limit_cone
    (Nominal.emptyCone_isLimit K) (Nominal.nominalInclusion_emptyCone_isLimit K)⟩

instance nominalInclusion_preservesFiniteProducts.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] :
    PreservesFiniteProducts.{v} (nominalInclusion 𝔸) :=
  ⟨λ _ ↦ preservesShape_fin_of_preserves_binary_and_terminal _ _⟩

def Nominal.equaliserCone.{v} [Infinite 𝔸] (K : WalkingParallelPair ⥤ Bundled.{v} (Nominal 𝔸)) :
    Cone K where
  pt := ⟨Equaliser (K.map .left) (K.map .right) (K.map .left).prop (K.map .right).prop,
    inferInstance⟩
  π := {
    app j := match j with
      | .zero => ⟨Equaliser.val (hf := (K.map .left).prop) (hg := (K.map .right).prop),
          Equaliser.val_equivariant⟩
      | .one => ⟨K.map .left ∘ Equaliser.val
            (hf := (K.map .left).prop) (hg := (K.map .right).prop),
          (K.map .left).prop.comp Equaliser.val_equivariant⟩
    naturality j k h := by
      ext x
      cases h
      case left => rfl
      case right =>
        simp only [ConcreteCategory.hom, id_eq, const_obj_obj, const_obj_map, Category.id_comp,
          Function.comp_apply]
        exact Subtype.prop x
      case id =>
        simp only [ConcreteCategory.hom, id_eq, const_obj_obj, walkingParallelPairHom_id,
          CategoryTheory.Functor.map_id, Category.id_comp, const_obj_map, Category.comp_id]
  }

def Nominal.equaliserCone_isLimit.{v} [Infinite 𝔸] (K : WalkingParallelPair ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit (equaliserCone K) where
  lift s := ⟨Equaliser.factor
    (K.map .left) (K.map .right) (K.map .left).prop (K.map .right).prop
    (s.π.app _)
    λ x ↦ (congr_arg (· x) (s.π.naturality .left)).symm.trans
      (congr_arg (· x) (s.π.naturality .right)),
    Equaliser.factor_equivariant (s.π.app .zero).prop⟩
  fac s j := by
    ext x
    cases j
    case zero => rfl
    case one => exact (congr_arg (· x) (s.π.naturality .left)).symm
  uniq s m h := by
    ext x
    have := congr_arg (· x) (h .zero)
    exact Subtype.coe_injective this

def Nominal.nominalInclusion_equaliserCone_isLimit.{v} [Infinite 𝔸] (K : WalkingParallelPair ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit ((nominalInclusion 𝔸).mapCone (equaliserCone K)) where
  lift s := ⟨Equaliser.factor
    (K.map .left) (K.map .right) (K.map .left).prop (K.map .right).prop
    (s.π.app _)
    λ x ↦ (congr_arg (· x) (s.π.naturality .left)).symm.trans
      (congr_arg (· x) (s.π.naturality .right)),
    Equaliser.factor_equivariant (s.π.app .zero).prop⟩
  fac s j := by
    ext x
    cases j
    case zero => rfl
    case one => exact (congr_arg (· x) (s.π.naturality .left)).symm
  uniq s m h := by
    ext x
    have := congr_arg (· x) (h .zero)
    exact Subtype.coe_injective this

instance nominalInclusion_preservesEqualisers.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    PreservesLimitsOfShape WalkingParallelPair (nominalInclusion.{v} 𝔸) :=
  ⟨λ {K} ↦ preservesLimit_of_preserves_limit_cone
    (Nominal.equaliserCone_isLimit K) (Nominal.nominalInclusion_equaliserCone_isLimit K)⟩

instance nominalInclusion_preservesFiniteLimits.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    PreservesFiniteLimits.{v} (nominalInclusion 𝔸) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _
