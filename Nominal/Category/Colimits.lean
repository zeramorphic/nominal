import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Nominal.Category.Defs

open CategoryTheory Functor Limits

variable {𝔸 : Type*} [DecidableEq 𝔸]

def Nominal.coproductCocone [Infinite 𝔸] {J : Type*} (K : Discrete J ⥤ Bundled (Nominal 𝔸)) :
    Cocone K where
  pt := ⟨(j : Discrete J) × K.obj j, inferInstance⟩
  ι := {
    app j := ⟨λ x ↦ ⟨j, x⟩,
      by intro π; ext x; rw [Function.perm_def, Sigma.perm_mk, perm_inv_perm]⟩
    naturality j k h := by cases Discrete.ext (Discrete.eq_of_hom h); simp
  }

def Nominal.coproductCocone_isColimit [Infinite 𝔸] {J : Type*}
    (K : Discrete J ⥤ Bundled (Nominal 𝔸)) :
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

instance Nominal.hasCoproducts.{v} [Infinite 𝔸] :
    HasCoproducts.{v} (Bundled.{v} (Nominal 𝔸)) :=
  λ _ ↦ ⟨λ K ↦ ⟨Nominal.coproductCocone K, Nominal.coproductCocone_isColimit K⟩⟩

def Nominal.coequaliserCocone [Infinite 𝔸] (K : WalkingParallelPair ⥤ Bundled (Nominal 𝔸)) :
    Cocone K where
  pt := ⟨Coequaliser (K.map .left) (K.map .right)
      (K.map .left).equivariant (K.map .right).equivariant,
    inferInstance⟩
  ι := {
    app j := match j with
      | .zero => ⟨Coequaliser.mk
          (hf := (K.map .left).equivariant) (hg := (K.map .right).equivariant) ∘
          K.map .right,
        Coequaliser.mk_equivariant.comp (K.map .right).equivariant⟩
      | .one => ⟨Coequaliser.mk (hf := (K.map .left).equivariant) (hg := (K.map .right).equivariant),
        Coequaliser.mk_equivariant⟩
    naturality j k h := by
      ext x
      cases h
      case left =>
        simp only [forget_hom, const_obj_obj, const_obj_map, Category.comp_id, Function.comp_apply]
        apply Coequaliser.condition
      case right => rfl
      case id =>
        simp only [forget_hom, const_obj_obj, walkingParallelPairHom_id,
          CategoryTheory.Functor.map_id, Category.id_comp, const_obj_map, Category.comp_id]
  }

def Nominal.coequaliserCocone_isColimit [Infinite 𝔸]
    (K : WalkingParallelPair ⥤ Bundled (Nominal 𝔸)) :
    IsColimit (coequaliserCocone K) where
  desc s := ⟨Coequaliser.factor
    (K.map .left) (K.map .right) (K.map .left).equivariant (K.map .right).equivariant
    (s.ι.app _)
    λ x ↦ (congr_arg (· x) (s.ι.naturality .left)).trans
      (congr_arg (· x) (s.ι.naturality .right)).symm,
    Coequaliser.factor_equivariant (s.ι.app .one).equivariant⟩
  fac s j := by
    ext x
    cases j
    case zero => exact congr_arg (· x) (s.ι.naturality .right)
    case one => rfl
  uniq s m h := by
    ext x
    obtain ⟨x, rfl⟩ := Coequaliser.mk_surjective
      (hf := (K.map .left).equivariant) (hg := (K.map .right).equivariant) x
    exact congr_arg (· x) (h .one)

instance Nominal.hasCoequalisers [Infinite 𝔸] :
    HasCoequalizers (Bundled (Nominal 𝔸)) :=
  ⟨λ F ↦ ⟨Nominal.coequaliserCocone F, Nominal.coequaliserCocone_isColimit F⟩⟩

instance Nominal.hasColimits.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    HasColimitsOfSize.{v, v} (Bundled.{v} (Nominal 𝔸)) :=
  has_colimits_of_hasCoequalizers_and_coproducts
