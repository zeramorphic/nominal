import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Nominal.Category.FinInj

/-!
# Colimits of shape `FinInj`

In this file, we construct the colimit in `Type` for a diagram of shape `FinInj`.
-/

open CategoryTheory Functor Limits

def finInjRel {𝔸 : Type*} (F : FinInj 𝔸 ⥤ Type*) (x y : (s : FinInj 𝔸) × F.obj s) : Prop :=
  ∃ (t : FinInj 𝔸) (f : x.1 ⟶ t) (g : y.1 ⟶ t), F.map f x.2 = F.map g y.2

instance finInjRel_refl {𝔸 : Type*} (F : FinInj 𝔸 ⥤ Type*) :
    IsRefl _ (finInjRel F) := by
  constructor
  intro x
  exact ⟨x.1, 𝟙 x.1, 𝟙 x.1, rfl⟩

instance finInjRel_symm {𝔸 : Type*} (F : FinInj 𝔸 ⥤ Type*) :
    IsSymm _ (finInjRel F) := by
  constructor
  rintro x y ⟨t, f, g, h⟩
  exact ⟨t, g, f, h.symm⟩

instance : Fintype WalkingPair where
  elems := {.left, .right}
  complete x := by cases x <;> decide

instance finInjRel_trans {𝔸 : Type*} [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type*) :
    IsTrans _ (finInjRel F) := by
  have : DecidableEq 𝔸 := Classical.typeDecidableEq 𝔸
  constructor
  intro x y z ⟨t₁, f₁, g₁, h₁⟩ ⟨t₂, f₂, g₂, h₂⟩
  have := FinInj.pushoutCocone (span g₁ f₂)
  refine ⟨(FinInj.pushoutCocone (span g₁ f₂)).pt,
    f₁ ≫ PushoutCocone.inl (FinInj.pushoutCocone (span g₁ f₂)),
    g₂ ≫ PushoutCocone.inr (FinInj.pushoutCocone (span g₁ f₂)), ?_⟩
  rw [FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply, h₁, ← h₂,
    ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
    PushoutCocone.condition]

theorem finInjRel_equivalence {𝔸 : Type*} [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type*) :
    Equivalence (finInjRel F) :=
  ⟨(finInjRel_refl F).refl, (finInjRel_symm F).symm _ _, (finInjRel_trans F).trans _ _ _⟩

def finInjSetoid {𝔸 : Type*} [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type*) :
    Setoid ((s : FinInj 𝔸) × F.obj s) where
  r := finInjRel F
  iseqv := finInjRel_equivalence F

def finInjColimitApex {𝔸 : Type*} [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type*) :=
  Quotient (finInjSetoid F)

def finInjCocone.{u, v} {𝔸 : Type u} [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type (max u v)) :
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

def finInjCocone_isColimit.{u, v} {𝔸 : Type u} [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type (max u v)) :
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

def finInjColimit.{u, v} (𝔸 : Type u) [Infinite 𝔸] :
    (FinInj 𝔸 ⥤ Type (max u v)) ⥤ Type (max u v) where
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

def finInjLeg.{u, v} {𝔸 : Type u} [Infinite 𝔸] {F : FinInj 𝔸 ⥤ Type (max u v)}
    (s : FinInj 𝔸) (x : F.obj s) :
    (finInjColimit 𝔸).obj F :=
  (finInjCocone F).ι.app s x

@[simp]
theorem finInjLeg_w.{u, v} {𝔸 : Type u} [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type (max u v))
    {s t : FinInj 𝔸} (f : s ⟶ t) :
    F.map f ≫ finInjLeg t = finInjLeg s :=
  (finInjCocone F).w f

@[elab_as_elim]
theorem finInjLeg_inductionOn.{u, v} {𝔸 : Type u} [Infinite 𝔸] {F : FinInj 𝔸 ⥤ Type (max u v)}
    {motive : (finInjColimit 𝔸).obj F → Prop}
    (q : (finInjColimit 𝔸).obj F)
    (h : (s : FinInj 𝔸) → (x : F.obj s) → motive (finInjLeg s x)) : motive q :=
  Quot.inductionOn q (λ x ↦ h x.1 x.2)

def finInjPermCocone {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type _)
    (π : Finperm 𝔸) :
    Cocone F where
  pt := (finInjColimit 𝔸).obj F
  ι := {
    app s := F.map ((finInjPermIso π).inv.app s) ≫ (finInjCocone F).ι.app (π ⬝ s)
    naturality {s t} f := by
      have := (isoWhiskerRight (finInjPermIso π) F).inv.naturality f
      simp only [comp_obj, id_obj, Functor.comp_map, Functor.id_map, isoWhiskerRight_inv,
        whiskerRight_app] at this
      simp only [const_obj_obj, const_obj_map, Category.comp_id]
      rw [← Category.assoc, this, Category.assoc]
      erw [(finInjCocone F).w ((finInjPermFunctor π).map f)]
      rfl
  }

theorem finInjPermCocone_ι_app_one {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type _)
    (s : FinInj 𝔸) :
    (finInjPermCocone F 1).ι.app s = (finInjCocone F).ι.app s :=
  (finInjCocone F).w ((finInjPermIso 1).inv.app s)

theorem finInjPermCocone_ι_app_mul {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type _)
    (π₁ π₂ : Finperm 𝔸) (s : FinInj 𝔸) :
    (finInjPermCocone F (π₁ * π₂)).ι.app s =
      (finInjPermCocone F π₂).ι.app s ≫
      (finInjCocone_isColimit F).desc (finInjPermCocone F π₁) := by
  simp only [finInjPermCocone, const_obj_obj, Category.assoc, IsColimit.fac]
  erw [(finInjCocone F).w ((finInjPermIso π₁).inv.app (π₂ ⬝ s)),
    (finInjCocone F).w ((finInjPermIso (π₁ * π₂)).inv.app s),
    (finInjCocone F).w ((finInjPermIso π₂).inv.app s)]

instance {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type _) :
    HasPerm 𝔸 ((finInjColimit 𝔸).obj F) where
  perm π := (finInjCocone_isColimit F).desc (finInjPermCocone F π)

theorem finInjColimit_perm_def {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : FinInj 𝔸 ⥤ Type _) (x : (finInjColimit 𝔸).obj F) (π : Finperm 𝔸) :
    π ⬝ x = (finInjCocone_isColimit F).desc (finInjPermCocone F π) x :=
  rfl

theorem finInjColimit_mk_perm {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : FinInj 𝔸 ⥤ Type _) (s : FinInj 𝔸) (x : F.obj s) (π : Finperm 𝔸) :
    π ⬝ finInjLeg s x = finInjLeg (π ⬝ s) (F.map ((finInjPermIso π).inv.app s) x) :=
  rfl

instance {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type _) :
    MulPerm 𝔸 ((finInjColimit 𝔸).obj F) where
  one_perm x := by
    rw [finInjColimit_perm_def, ← (finInjCocone_isColimit F).uniq]
    intro s
    change (finInjCocone F).ι.app s = _
    rw [finInjPermCocone_ι_app_one]
  mul_perm π₁ π₂ x := by
    simp only [finInjColimit_perm_def]
    rw [← (finInjCocone_isColimit F).uniq]
    intro s
    rw [finInjPermCocone_ι_app_mul]
    rfl
