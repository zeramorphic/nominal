import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Nominal.Category.Defs

open CategoryTheory Functor Limits

variable {𝔸 : Type*} [DecidableEq 𝔸]

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
    · apply (apply_perm_eq (s.π.app ⟨.left⟩).equivariant π _).trans
      rw [perm_inv_perm]
      rfl
    · apply (apply_perm_eq (s.π.app ⟨.right⟩).equivariant π _).trans
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

def Nominal.emptyCone.{v} (K : Discrete PEmpty ⥤ Bundled.{v} (Nominal 𝔸)) :
    Cone K where
  pt := ⟨PUnit, inferInstance⟩
  π := {
    app j := j.as.elim
  }

def Nominal.emptyCone_isLimit.{v} (K : Discrete PEmpty ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit (emptyCone K) where
  lift s := ⟨λ _ ↦ PUnit.unit, λ _ ↦ rfl⟩

def Nominal.productCone {J : Type*} (K : Discrete J ⥤ Bundled (Nominal 𝔸)) :
    Cone K where
  pt := ⟨Product 𝔸 (K.obj ·), inferInstance⟩
  π := {
    app j := ⟨Product.pr j, Product.pr_equivariant j⟩
    naturality j k h := by cases Discrete.ext (Discrete.eq_of_hom h); simp
  }

def Nominal.productCone_isLimit [Infinite 𝔸] {J : Type*} (K : Discrete J ⥤ Bundled (Nominal 𝔸)) :
    IsLimit (productCone K) where
  lift s := ⟨λ x ↦ ⟨⟨λ i ↦ s.π.app i x⟩,
    by
      use supp 𝔸 x
      intro π h
      ext i
      exact (Nominal.supp_supports 𝔸 x).map _ (s.π.app i).equivariant π h⟩,
    by
      intro π
      ext x
      apply FS.ext
      apply PointProduct.ext
      ext i
      exact (congr_arg (π ⬝ ·) (apply_perm_eq (s.π.app i).equivariant π⁻¹ x)).symm.trans
        (perm_inv_perm _ _)⟩
  uniq s m h := by
    ext x : 3
    apply FS.ext
    apply PointProduct.ext
    funext i
    simp only [forget_hom, const_obj_obj, FS.val_mk', ← h]
    rfl

instance Nominal.hasProducts.{v} [Infinite 𝔸] :
    HasProducts.{v} (Bundled.{v} (Nominal 𝔸)) :=
  λ _ ↦ ⟨λ K ↦ ⟨Nominal.productCone K, Nominal.productCone_isLimit K⟩⟩

def Nominal.equaliserCone.{v} [Infinite 𝔸] (K : WalkingParallelPair ⥤ Bundled.{v} (Nominal 𝔸)) :
    Cone K where
  pt := ⟨Equaliser (K.map .left) (K.map .right)
      (K.map .left).equivariant (K.map .right).equivariant,
    inferInstance⟩
  π := {
    app j := match j with
      | .zero => ⟨Equaliser.val
            (hf := (K.map .left).equivariant) (hg := (K.map .right).equivariant),
          Equaliser.val_equivariant⟩
      | .one => ⟨K.map .left ∘ Equaliser.val
            (hf := (K.map .left).equivariant) (hg := (K.map .right).equivariant),
          (K.map .left).equivariant.comp Equaliser.val_equivariant⟩
    naturality j k h := by
      ext x
      cases h
      case left => rfl
      case right =>
        simp only [forget_hom, const_obj_obj, const_obj_map, Category.id_comp,
          Function.comp_apply]
        exact Subtype.prop x
      case id =>
        simp only [forget_hom, const_obj_obj, walkingParallelPairHom_id,
          CategoryTheory.Functor.map_id, Category.id_comp, const_obj_map, Category.comp_id]
  }

def Nominal.equaliserCone_isLimit.{v} [Infinite 𝔸]
    (K : WalkingParallelPair ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit (equaliserCone K) where
  lift s := ⟨Equaliser.factor
    (K.map .left) (K.map .right) (K.map .left).equivariant (K.map .right).equivariant
    (s.π.app _)
    λ x ↦ (congr_arg (· x) (s.π.naturality .left)).symm.trans
      (congr_arg (· x) (s.π.naturality .right)),
    Equaliser.factor_equivariant (s.π.app .zero).equivariant⟩
  fac s j := by
    cases j
    case zero => rfl
    case one => exact s.w .left
  uniq s m h := by
    ext x
    have := congr_arg (· x) (h .zero)
    exact Subtype.coe_injective this

instance Nominal.hasEqualisers [Infinite 𝔸] :
    HasEqualizers (Bundled (Nominal 𝔸)) :=
  ⟨λ F ↦ ⟨Nominal.equaliserCone F, Nominal.equaliserCone_isLimit F⟩⟩

instance Nominal.hasLimits.{v} [Infinite 𝔸] :
    HasLimitsOfSize.{v, v} (Bundled.{v} (Nominal 𝔸)) :=
  has_limits_of_hasEqualizers_and_products
