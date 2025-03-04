import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
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
  have := FinInj.spanCocone (span g₁ f₂)
  refine ⟨(FinInj.spanCocone (span g₁ f₂)).pt,
    f₁ ≫ PushoutCocone.inl (FinInj.spanCocone (span g₁ f₂)),
    g₂ ≫ PushoutCocone.inr (FinInj.spanCocone (span g₁ f₂)), ?_⟩
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

def finInjColimit {α : Type*} [Infinite α] (F : FinInj α ⥤ Type*) :=
  Quotient (finInjSetoid F)
