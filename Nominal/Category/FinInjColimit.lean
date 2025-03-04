import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Nominal.Category.FinInj

/-!
# Colimits of shape `FinInj`

In this file, we construct the colimit in `Type` for a diagram of shape `FinInj`.
-/

open CategoryTheory Functor Limits

def finInjRel {α : Type*} (F : FinInj α ⥤ Type*) (x y : (s : FinInj α) × F.obj s) : Prop :=
  ∃ (t : FinInj α) (f : x.1 ⟶ t) (g : y.1 ⟶ t), F.map f x.2 = F.map g y.2

instance finInjRel_refl {α : Type*} (F : FinInj α ⥤ Type*) :
    IsRefl _ (finInjRel F) := by
  constructor
  intro x
  exact ⟨x.1, 𝟙 x.1, 𝟙 x.1, rfl⟩

instance finInjRel_symm {α : Type*} (F : FinInj α ⥤ Type*) :
    IsSymm _ (finInjRel F) := by
  constructor
  rintro x y ⟨t, f, g, h⟩
  exact ⟨t, g, f, h.symm⟩

instance : Fintype WalkingPair where
  elems := {.left, .right}
  complete x := by cases x <;> decide

instance finInjRel_trans {α : Type*} [Infinite α] (F : FinInj α ⥤ Type*) :
    IsTrans _ (finInjRel F) := by
  have : DecidableEq α := Classical.typeDecidableEq α
  constructor
  intro x y z ⟨t₁, f₁, g₁, h₁⟩ ⟨t₂, f₂, g₂, h₂⟩
  have := FinInj.pushoutCocone (span g₁ f₂)
  refine ⟨(FinInj.pushoutCocone (span g₁ f₂)).pt,
    f₁ ≫ PushoutCocone.inl (FinInj.pushoutCocone (span g₁ f₂)),
    g₂ ≫ PushoutCocone.inr (FinInj.pushoutCocone (span g₁ f₂)), ?_⟩
  rw [FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply, h₁, ← h₂,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    PushoutCocone.condition]

theorem finInjRel_equivalence {α : Type*} [Infinite α] (F : FinInj α ⥤ Type*) :
    Equivalence (finInjRel F) :=
  ⟨(finInjRel_refl F).refl, (finInjRel_symm F).symm _ _, (finInjRel_trans F).trans _ _ _⟩

def finInjSetoid {α : Type*} [Infinite α] (F : FinInj α ⥤ Type*) :
    Setoid ((s : FinInj α) × F.obj s) where
  r := finInjRel F
  iseqv := finInjRel_equivalence F

def finInjColimitApex {α : Type*} [Infinite α] (F : FinInj α ⥤ Type*) :=
  Quotient (finInjSetoid F)

def finInjCocone.{u, v} {α : Type u} [Infinite α] (F : FinInj α ⥤ Type (max u v)) :
    Cocone F where
  pt := finInjColimitApex F
  ι := {
    app s x := Quotient.mk (finInjSetoid F) ⟨s, x⟩
    naturality s t f := by
      ext x
      simp only [const_obj_obj, types_comp_apply, const_obj_map, types_id_apply]
      apply Quotient.sound
      refine ⟨t, 𝟙 t, f, ?_⟩
      simp only [FunctorToTypes.map_id_apply]
  }

def finInjCocone_isColimit.{u, v} {α : Type u} [Infinite α] (F : FinInj α ⥤ Type (max u v)) :
    IsColimit (finInjCocone F) where
  desc c := Quotient.lift (λ x ↦ c.ι.app x.1 x.2) <| by
    rintro ⟨s, x⟩ ⟨t, y⟩ ⟨u, f, g, h⟩
    dsimp only
    rw [← c.w f, ← c.w g, types_comp_apply, h]
    rfl
  fac c s := by
    ext x
    simp only [finInjCocone, const_obj_obj, types_comp_apply, Quotient.lift_mk]
  uniq c m h := by
    ext x
    induction x using Quotient.inductionOn
    case h x =>
    simp only [Quotient.lift_mk]
    rw [← h x.1]
    rfl

def finInjColimit.{u, v} {α : Type u} [Infinite α] :
    (FinInj α ⥤ Type (max u v)) ⥤ Type (max u v) where
  obj := finInjColimitApex
  map a := Quotient.lift (λ x ↦ Quotient.mk _ ⟨x.1, a.app x.1 x.2⟩) <| by
    rintro ⟨s, x⟩ ⟨t, y⟩ ⟨u, f, g, h⟩
    apply Quotient.sound
    refine ⟨u, f, g, ?_⟩
    simp only
    refine (congr_arg (· x) (a.naturality f)).symm.trans ?_
    rw [types_comp_apply, h]
    exact (congr_arg (· y) (a.naturality g))
  map_id β := by
    ext x
    induction x using Quotient.inductionOn
    case h x =>
    simp only [types_comp_apply, id_eq, eq_mpr_eq_cast, cast_eq, NatTrans.id_app, types_id_apply,
      Sigma.eta, Quotient.lift_mk]
  map_comp f g := by
    ext x
    induction x using Quotient.inductionOn
    case h x =>
    simp only [types_comp_apply, id_eq, eq_mpr_eq_cast, cast_eq, FunctorToTypes.comp,
      Quotient.lift_mk]
