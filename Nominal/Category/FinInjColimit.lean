import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Nominal.Category.FinInj

/-!
# Colimits of shape `FinInj`

In this file, we construct the colimit in `Type` for a diagram of shape `FinInj`.
Our main objective is to construct the functor
`finInjToNominal : (FinInj 𝔸 ⥤ Type) ⥤ Bundled (Nominal 𝔸)`.
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
  map {F G} f := (finInjCocone_isColimit F).desc ((Cocones.precompose f).obj (finInjCocone G))
  map_id F := by
    dsimp only
    rw [← (finInjCocone_isColimit F).uniq]
    intro
    rfl
  map_comp {F G H} f g := by
    dsimp only
    rw [← (finInjCocone_isColimit F).uniq]
    intro
    rfl

theorem finInjColimit_map.{u, v} (𝔸 : Type u) [Infinite 𝔸] {F G : FinInj 𝔸 ⥤ Type (max u v)}
    (f : F ⟶ G) :
    (finInjColimit 𝔸).map f =
    (finInjCocone_isColimit F).desc ((Cocones.precompose f).obj (finInjCocone G)) :=
  rfl

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

/-- We define the permutation action of `Finperm 𝔸` on the colimit of a functor `FinInj 𝔸 ⥤ Type _`
by the universal property of the colimit. This avoids dealing with any heterogeneous equalities
or transports. -/
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

theorem supports_finInjLeg {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸] {F : FinInj 𝔸 ⥤ Type _}
    (s : FinInj 𝔸) (x : F.obj s) :
    Supports s.val (finInjLeg s x) := by
  intro π hπ
  rw [finInjColimit_perm_def, finInjLeg,
    ← (finInjCocone_isColimit F).uniq (finInjPermCocone F π) (𝟙 ((finInjCocone F).pt)),
    types_id_apply]
  intro j
  exact ((finInjCocone F).w ((finInjPermIso π).inv.app j)).symm

instance {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸] (F : FinInj 𝔸 ⥤ Type _) :
    Nominal 𝔸 ((finInjColimit 𝔸).obj F) where
  supported x := by
    induction x using finInjLeg_inductionOn
    case h s x =>
    exact ⟨_, supports_finInjLeg s x⟩

theorem finInjColimit_map_equivariant' {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    {F G : FinInj 𝔸 ⥤ Type _} (f : F ⟶ G) (π : Finperm 𝔸) :
    (finInjCocone_isColimit F).desc (finInjPermCocone F π) ≫
      (finInjCocone_isColimit F).desc ((Cocones.precompose f).obj (finInjCocone G)) =
    (finInjCocone_isColimit F).desc ((Cocones.precompose f).obj (finInjCocone G)) ≫
        (finInjCocone_isColimit G).desc (finInjPermCocone G π) := by
  trans (finInjCocone_isColimit F).desc ((Cocones.precompose f).obj (finInjPermCocone G π))
  · apply (finInjCocone_isColimit F).uniq
      ((Cocones.precompose f).obj (finInjPermCocone G π))
    intro s
    have := f.naturality ((finInjPermIso π).inv.app s)
    simp only [finInjPermCocone, const_obj_obj, Cocones.precompose_obj_pt, IsColimit.fac_assoc,
      Category.assoc, IsColimit.fac, Cocones.precompose_obj_ι, NatTrans.comp_app]
    simp only [id_obj, finInjPermFunctor] at this
    rw [← Category.assoc, this]
    rfl
  · symm
    apply (finInjCocone_isColimit F).uniq
      ((Cocones.precompose f).obj (finInjPermCocone G π))
    intro s
    simp only [Cocones.precompose_obj_pt, const_obj_obj, IsColimit.fac_assoc,
      Cocones.precompose_obj_ι, NatTrans.comp_app, Category.assoc, IsColimit.fac]

theorem finInjColimit_map_equivariant {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    {F G : FinInj 𝔸 ⥤ Type _} (f : F ⟶ G) :
    Equivariant 𝔸 (α := (finInjColimit 𝔸).obj F → (finInjColimit 𝔸).obj G)
      ((finInjColimit 𝔸).map f) := by
  intro π
  ext x
  rw [Function.perm_def, perm_eq_iff_eq_inv_perm, finInjColimit_map, finInjColimit_perm_def,
    finInjColimit_perm_def]
  rw [← types_comp_apply _ ((finInjCocone_isColimit F).desc _),
    ← types_comp_apply _ ((finInjCocone_isColimit G).desc _),
    finInjColimit_map_equivariant']

def finInjToNominal.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    (FinInj 𝔸 ⥤ Type (max u v)) ⥤ Bundled.{max u v} (Nominal 𝔸) where
  obj F := ⟨(finInjColimit 𝔸).obj F, inferInstance⟩
  map {F G} f := ⟨(finInjColimit 𝔸).map f, finInjColimit_map_equivariant f⟩
  map_id F := by
    apply EQ.ext
    exact (finInjColimit 𝔸).map_id F
  map_comp f g := by
    apply EQ.ext
    exact (finInjColimit 𝔸).map_comp f g
