import Mathlib.CategoryTheory.Adjunction.Reflective
import Nominal.Category.Defs

open CategoryTheory Functor Limits

variable {𝔸 : Type*} [DecidableEq 𝔸]

def nominalInclusion.{u} (𝔸 : Type*) [DecidableEq 𝔸] :
    Bundled.{u} (Nominal 𝔸) ⥤ Bundled.{u} (MulPerm 𝔸) where
  obj := Bundled.map (λ x ↦ x.toMulPerm)
  map := id

def nominalCoreflection.{u} (𝔸 : Type*) [DecidableEq 𝔸] :
    Bundled.{u} (MulPerm 𝔸) ⥤ Bundled.{u} (Nominal 𝔸) where
  obj α := Nominal.of (FS 𝔸 α)
  map {X Y} f := ⟨(f.equivariant.comp FS.val_equivariant).toFS,
    (f.equivariant.comp FS.val_equivariant).toFS_equivariant⟩

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
    app j := ⟨λ x ↦ ⟨j, x⟩,
      by intro π; ext x; rw [Function.perm_def, Sigma.perm_mk, perm_inv_perm]⟩
    naturality j k h := by cases Discrete.ext (Discrete.eq_of_hom h); simp
  }

def MulPerm.coproductCocone_isColimit {J : Type*} (K : Discrete J ⥤ Bundled (MulPerm 𝔸)) :
    IsColimit (coproductCocone K) where
  desc s := ⟨λ x ↦ s.ι.app x.fst x.snd, by
    intro π
    ext x
    apply (apply_perm_eq (s.ι.app (π⁻¹ ⬝ x).fst).equivariant π (π⁻¹ ⬝ x).snd).trans
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
    apply (apply_perm_eq (s.ι.app (π⁻¹ ⬝ x).val.fst).equivariant π _).trans
    apply congr_arg (s.ι.app _)
    exact perm_inv_perm π (show FS 𝔸 _ from ⟨x.val.snd, Sigma.snd_finitelySupported x.prop⟩)⟩
  uniq := by
    intro s m h
    ext x
    simp only [mapCocone_pt, Nominal.forget_hom, id_eq, comp_obj, const_obj_obj]
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
