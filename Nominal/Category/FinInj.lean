import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.Data.Finite.Sum
import Mathlib.Logic.Embedding.Basic
import Nominal.Category.Defs

/-!
# The category of finite sets and injections

This small category is not filtered, but has a cocone for every span.
Fortunately, this is enough to make the usual construction of filtered colimits work.
-/

open CategoryTheory Function Functor Limits Finset

@[ext]
structure FinInj (𝔸 : Type*) where
  val : Finset 𝔸

open FinInj

attribute [coe] FinInj.val

instance {𝔸 : Type*} : Category (FinInj 𝔸) where
  Hom s t := s.val ↪ t.val
  id s := Embedding.refl s.val
  comp := Embedding.trans

instance {𝔸 : Type*} {s t : FinInj 𝔸} :
    FunLike (s ⟶ t) s.val t.val :=
  inferInstanceAs (FunLike (s.val ↪ t.val) s.val t.val)

@[simp]
theorem FinInj.id_coe {𝔸 : Type*} (s : FinInj 𝔸) :
    ((𝟙 s : s ⟶ s) : s.val → s.val) = id :=
  rfl

@[simp]
theorem FinInj.comp_coe {𝔸 : Type*} {s t u : FinInj 𝔸} (f : s ⟶ t) (g : t ⟶ u) :
    ((f ≫ g) : s.val → u.val) = g ∘ f :=
  rfl

@[simp]
theorem FinInj.apply_eq_iff_eq {𝔸 : Type*} {s t : FinInj 𝔸} {f : s ⟶ t} (x y : s.val) :
    f x = f y ↔ x = y :=
  f.apply_eq_iff_eq x y

@[simp]
theorem FinInj.mk_coe_eq {𝔸 : Type*} {s t : FinInj 𝔸}
    (f : s.val → t.val) (h : Function.Injective f) :
    ((⟨f, h⟩ : s ⟶ t) : s.val → t.val) = f :=
  rfl

@[simp]
theorem FinInj.mk_apply_eq {𝔸 : Type*} {s t : FinInj 𝔸}
    (f : s.val → t.val) (h : Function.Injective f) (x : s.val) :
    (⟨f, h⟩ : s ⟶ t) x = f x :=
  rfl

instance {𝔸 : Type*} : Nonempty (FinInj 𝔸) :=
  ⟨⟨∅⟩⟩

/-!
## Pullbacks
-/

def FinInj.pullbackConeApex {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) :
    FinInj 𝔸 :=
  ⟨((F.obj (some .left)).val.attach.filter
    (λ x ↦ ∃ y, F.map (.term .left) x = F.map (.term .right) y)).map
    (Embedding.subtype _)⟩

theorem FinInj.mem_pullbackConeApex_iff {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) (x : 𝔸) :
    x ∈ (pullbackConeApex F).val ↔
      ∃ (h : x ∈ (F.obj (some .left)).val),
      ∃ y, F.map (.term .left) ⟨x, h⟩ = F.map (.term .right) y := by
  simp only [pullbackConeApex, Subtype.exists, mem_map, mem_filter, mem_attach, true_and,
    Embedding.coe_subtype, exists_and_right, exists_eq_right]

def FinInj.pullbackConeMapNone {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) :
    pullbackConeApex F ⟶ F.obj none where
  toFun x := ⟨F.map (.term .left) ⟨x,
    by
      have := x.prop
      rw [mem_pullbackConeApex_iff] at this
      obtain ⟨hx, y, h⟩ := this
      exact hx⟩,
    Finset.coe_mem _⟩
  inj' := by
    rintro ⟨y, hy⟩ ⟨z, hz⟩ h
    rw [mem_pullbackConeApex_iff] at hy hz
    simp only [Subtype.mk.injEq] at h
    obtain ⟨hy, a, ha⟩ := hy
    obtain ⟨hz, b, hb⟩ := hz
    rw [ha, hb] at h
    have := (F.map (.term .right)).injective (Subtype.coe_injective h)
    rw [Subtype.mk.injEq] at this
    cases Subtype.coe_injective this
    rw [← hb] at ha
    have := (F.map (.term .left)).injective ha
    rw [Subtype.mk.injEq] at this
    cases this
    rfl

def FinInj.pullbackConeMapLeft {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) :
    pullbackConeApex F ⟶ F.obj (some .left) where
  toFun x := ⟨x,
    by
      have := x.prop
      rw [mem_pullbackConeApex_iff] at this
      obtain ⟨hx, y, hy⟩ := this
      exact hx⟩
  inj' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    rw [mem_pullbackConeApex_iff] at hx hy
    simp only [Subtype.mk.injEq] at h
    cases h
    rfl

def FinInj.pullbackConeMapRight' {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) (x : (pullbackConeApex F).val) :
    (F.obj (some .right)).val :=
  (F.obj (some .right)).val.attach.choose
  (λ y ↦ F.map (.term .left) (pullbackConeMapLeft F x) = F.map (.term .right) y) <| by
    have := x.prop
    rw [mem_pullbackConeApex_iff] at this
    obtain ⟨hx, y, hy⟩ := this
    refine ⟨y, ⟨mem_attach _ _, hy⟩, ?_⟩
    rintro ⟨z, hz⟩ ⟨hz', h'⟩
    exact (F.map (.term .right)).injective (h'.symm.trans hy)

theorem FinInj.pullbackConeMapRight'_property {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) (x : (pullbackConeApex F).val) :
    F.map (.term .left) (pullbackConeMapLeft F x) =
    F.map (.term .right) (pullbackConeMapRight' F x) :=
  (F.obj (some .right)).val.attach.choose_property
    (λ y ↦ F.map (.term .left) (pullbackConeMapLeft F x) = F.map (.term .right) y) _

def FinInj.pullbackConeMapRight {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) :
    pullbackConeApex F ⟶ F.obj (some .right) where
  toFun := pullbackConeMapRight' F
  inj' := by
    intro x y h
    apply (pullbackConeMapLeft F).injective
    apply (F.map (.term .left)).injective
    apply (pullbackConeMapRight'_property F x).trans
    exact (h ▸ pullbackConeMapRight'_property F y).symm

theorem FinInj.pullbackConeMapRight_comp {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) :
    pullbackConeMapRight F ≫ F.map (.term WalkingPair.right) = pullbackConeMapNone F := by
  apply DFunLike.coe_injective
  ext x : 1
  exact (pullbackConeMapRight'_property F x).symm

def FinInj.pullbackCone {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) :
    Cone F where
  pt := pullbackConeApex F
  π := {
    app x := match x with
      | none => pullbackConeMapNone F
      | some .left => pullbackConeMapLeft F
      | some .right => pullbackConeMapRight F
    naturality {s t} f := by
      cases f
      case id =>
        simp only [const_obj_obj, WidePullbackShape.hom_id, const_obj_map, Category.id_comp,
          CategoryTheory.Functor.map_id, Category.comp_id]
      case term i =>
        cases i
        case left => rfl
        case right =>
          simp only [const_obj_obj, const_obj_map, Category.id_comp, pullbackConeMapRight_comp]
  }

def FinInj.pullbackConeLift {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) (s : Cone F) :
    s.pt ⟶ pullbackConeApex F :=
  ⟨λ x ↦ ⟨s.π.app (some .left) x,
    by
      rw [mem_pullbackConeApex_iff]
      refine ⟨?_, s.π.app (some .right) x, ?_⟩
      · simp only [const_obj_obj, coe_mem]
      · exact (congr_arg (· x) (s.w (.term .left))).trans (congr_arg (· x) (s.w (.term .right))).symm⟩,
    by
      intro x y h
      simp only [const_obj_obj, Subtype.mk.injEq] at h
      exact (s.π.app (some .left)).injective (Subtype.coe_injective h)⟩

def FinInj.pullbackCone_isLimit {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingCospan ⥤ FinInj 𝔸) :
    IsLimit (pullbackCone F) where
  lift := pullbackConeLift F
  fac s j := by
    apply DFunLike.coe_injective
    ext x : 1
    cases j with
    | none => exact congr_arg (· x) (s.w (.term .left))
    | some j =>
      cases j with
      | left => rfl
      | right =>
        apply (F.map (.term .right)).injective
        have h₁ := congr_arg (· (pullbackConeLift F s x)) ((pullbackCone F).w (.term .right))
        have h₂ := congr_arg (· x) (s.w (.term .right))
        have h₃ := congr_arg (· x) (s.w (.term .left))
        exact (h₁.trans h₃).trans h₂.symm
  uniq s m h := by
    apply DFunLike.coe_injective
    ext x : 2
    simp only [pullbackConeLift, const_obj_obj]
    change _ = (s.π.app (some .left) x).val
    rw [← h]
    rfl

instance FinInj.hasPullbacks {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸] :
    HasLimitsOfShape WalkingCospan (FinInj 𝔸) :=
  ⟨λ F ↦ ⟨_, pullbackCone_isLimit F⟩⟩

/-!
## Pushout cocones
-/

inductive FinInj.SpanCoconeApex {𝔸 : Type*} [DecidableEq 𝔸]
    (F : WalkingSpan ⥤ FinInj 𝔸) where
  | inl : (F.obj (some .left)).val → FinInj.SpanCoconeApex F
  | inr' : (y : (F.obj (some .right)).val) → (∀ x, y ≠ F.map (.init .right) x) →
      FinInj.SpanCoconeApex F

noncomputable def FinInj.SpanCoconeApex.inr {𝔸 : Type*} [DecidableEq 𝔸]
    {F : WalkingSpan ⥤ FinInj 𝔸} (y : (F.obj (some .right)).val) : SpanCoconeApex F :=
  if h : ∃ x, y = F.map (.init .right) x then
    .inl (F.map (.init .left) h.choose)
  else
    .inr' y (by push_neg at h; exact h)

theorem FinInj.SpanCoconeApex.inr_injective {𝔸 : Type*} [DecidableEq 𝔸]
    {F : WalkingSpan ⥤ FinInj 𝔸} :
    Function.Injective (.inr : (F.obj (some .right)).val → SpanCoconeApex F) := by
  intro x y h
  rw [inr, inr] at h
  split_ifs at h with h₁ h₂
  case pos =>
    rw [inl.injEq, apply_eq_iff_eq] at h
    rw [h₁.choose_spec, h₂.choose_spec, h]
  case neg =>
    cases h
    rfl

theorem FinInj.SpanCoconeApex.inl_eq_inr {𝔸 : Type*} [DecidableEq 𝔸]
    {F : WalkingSpan ⥤ FinInj 𝔸} (x : (F.obj none).val) :
    SpanCoconeApex.inl (F.map (.init .left) x) =
      SpanCoconeApex.inr (F.map (.init .right) x) := by
  have : ∃ y, F.map (.init .right) x = F.map (.init .right) y := ⟨x, rfl⟩
  rw [inr, dif_pos this, inl.injEq, apply_eq_iff_eq]
  exact (F.map (.init .right)).injective this.choose_spec

instance {𝔸 : Type*} [DecidableEq 𝔸] (F : WalkingSpan ⥤ FinInj 𝔸) :
    Finite (SpanCoconeApex F) := by
  refine Finite.of_injective (β := (F.obj (some .left)).val ⊕ (F.obj (some .right)).val)
    (λ x ↦ match x with
      | .inl x => .inl x
      | .inr' x _ => .inr x) ?_
  intro x y h
  aesop

theorem Finset.exists_equiv_of_finite (𝔸 : Type*) [Infinite 𝔸] (β : Type*) [inst : Finite β] :
    Nonempty ((s : Finset 𝔸) × (β ≃ s)) := by
  rw [finite_iff_exists_equiv_fin] at inst
  obtain ⟨n, ⟨e⟩⟩ := inst
  obtain ⟨s, h⟩ := Infinite.exists_subset_card_eq 𝔸 n
  exact ⟨⟨s, e.trans (s.equivFinOfCardEq h).symm⟩⟩

noncomputable def Finset.chosenOfFinite (𝔸 : Type*) [Infinite 𝔸] (β : Type*) [Finite β] :
    Finset 𝔸 :=
  (exists_equiv_of_finite 𝔸 β).some.fst

noncomputable def Finset.equivOfFinite {𝔸 : Type*} [Infinite 𝔸] {β : Type*} [Finite β] :
    β ≃ chosenOfFinite 𝔸 β :=
  (exists_equiv_of_finite 𝔸 β).some.snd

/--
This is not a colimiting cocone. Indeed, consider the other cocone `c` given by
```
∅   → {x}
↓      ↓
{x} → {x}
```
The map of apexes from this cocone to `c` is not injective, so this cocone is not colimiting.
-/
noncomputable def FinInj.pushoutCocone {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (F : WalkingSpan ⥤ FinInj 𝔸) :
    Cocone F where
  pt := ⟨chosenOfFinite 𝔸 (SpanCoconeApex F)⟩
  ι := {
    app x := match x with
      | none => ⟨λ x ↦ equivOfFinite (.inl (F.map (.init .left) x)), by
          intro x y h
          simp only [const_obj_obj, EmbeddingLike.apply_eq_iff_eq, SpanCoconeApex.inl.injEq] at h
          exact (F.map (.init .left)).injective h⟩
      | some .left => ⟨λ x ↦ equivOfFinite (.inl x), by
          intro x y h
          simp only [const_obj_obj, EmbeddingLike.apply_eq_iff_eq, SpanCoconeApex.inl.injEq] at h
          exact h⟩
      | some .right => ⟨λ x ↦ equivOfFinite (.inr x), by
          intro x y h
          simp only [const_obj_obj, EmbeddingLike.apply_eq_iff_eq,
            SpanCoconeApex.inr_injective.eq_iff] at h
          exact h⟩
    naturality x y f := by
      apply DFunLike.coe_injective
      cases f
      case a.id =>
        simp only [const_obj_obj, WidePushoutShape.hom_id, CategoryTheory.Functor.map_id,
          Category.id_comp, const_obj_map, Category.comp_id]
      case a.init i =>
        cases i
        case left => rfl
        case right =>
          ext x
          simp only [const_obj_obj, CategoryStruct.comp, SpanCoconeApex.inl_eq_inr, const_obj_map,
            CategoryStruct.id]
          rfl
  }

/-!
## Permutation actions
-/

instance {𝔸 : Type*} [DecidableEq 𝔸] : Nominal 𝔸 (FinInj 𝔸) where
  perm π s := ⟨π ⬝ s.val⟩
  one_perm s := FinInj.ext (one_perm s.val)
  mul_perm π₁ π₂ s := FinInj.ext (mul_perm π₁ π₂ s.val)
  supported s := by
    refine ⟨s.val, ?_⟩
    intro π h
    ext a : 2
    simp only [mem_perm, Finperm.perm_name_eq]
    constructor
    · intro ha
      have := h _ ha
      rw [Finperm.apply_inv_self] at this
      rwa [← this] at ha
    · intro ha
      rwa [← h _ ha, Finperm.inv_apply_self]

@[simp]
theorem FinInj.perm_val {𝔸 : Type*} [DecidableEq 𝔸] (π : Finperm 𝔸) (s : FinInj 𝔸) :
    (π ⬝ s).val = π ⬝ s.val :=
  rfl

def FinInj.isoOfEq {𝔸 : Type*} {s t : FinInj 𝔸} (h : s = t) :
    s ≅ t where
  hom := ⟨λ x ↦ ⟨x, by rw [← h]; exact x.prop⟩, λ x y h ↦ by
      apply Subtype.coe_injective
      have := congr_arg Subtype.val h
      exact this⟩
  inv := ⟨λ x ↦ ⟨x, by rw [h]; exact x.prop⟩, λ x y h ↦ by
      apply Subtype.coe_injective
      have := congr_arg Subtype.val h
      exact this⟩

def FinInj.permIso {𝔸 : Type*} [DecidableEq 𝔸] (π : Finperm 𝔸) (s : FinInj 𝔸) :
    π ⬝ s ≅ s where
  hom := ⟨λ x ↦ ⟨π⁻¹ x, by have := x.prop; simp only [perm_val, Finset.mem_perm] at this; exact this⟩,
    λ x y h ↦ Subtype.coe_injective (EmbeddingLike.injective π⁻¹ (congr_arg (λ x ↦ x.val) h))⟩
  inv := ⟨λ x ↦ ⟨π x, by rw [← Finperm.perm_name_eq, ← inv_inv π, ← Finset.mem_perm,
      inv_inv, perm_val, inv_perm_perm]; exact x.prop⟩,
    λ x y h ↦ Subtype.coe_injective (EmbeddingLike.injective π (congr_arg (λ x ↦ x.val) h))⟩
  hom_inv_id := by
    apply DFunLike.coe_injective
    ext x
    exact perm_inv_perm π _
  inv_hom_id := by
    apply DFunLike.coe_injective
    ext x
    exact inv_perm_perm π _

def finInjPermFunctor {𝔸 : Type*} [DecidableEq 𝔸] (π : Finperm 𝔸) :
    FinInj 𝔸 ⥤ FinInj 𝔸 where
  obj s := π ⬝ s
  map {s t} f := (permIso π s).hom ≫ f ≫ (permIso π t).inv

/-- The action of a finite permutation of atoms induces an equivalence of categories. -/
def finInjPerm {𝔸 : Type*} [DecidableEq 𝔸] (π : Finperm 𝔸) :
    FinInj 𝔸 ≌ FinInj 𝔸 where
  functor := finInjPermFunctor π
  inverse := finInjPermFunctor π⁻¹
  unitIso := {
    hom := {
      app s := (isoOfEq (inv_perm_perm π s)).inv
      naturality {s t} f := by
        apply DFunLike.coe_injective
        ext x
        change (f _).val = π⁻¹ ⬝ π ⬝ f _
        rw [inv_perm_perm]
        congr
        simp only [perm_val, permIso, finInjPermFunctor, inv_inv, id_obj, comp_obj, isoOfEq,
          Embedding.coeFn_mk, Finperm.inv_apply_self, Subtype.coe_eta]
    }
    inv := {
      app s := (isoOfEq (inv_perm_perm π s)).hom
      naturality {s t} f := by
        apply DFunLike.coe_injective
        ext x
        change π⁻¹ ⬝ π ⬝ f _ = (f _).val
        rw [inv_perm_perm]
        congr 2
        simp only [perm_val, permIso, finInjPermFunctor, inv_inv, Embedding.coeFn_mk,
          Finperm.inv_apply_self, comp_obj, id_obj, isoOfEq]
    }
  }
  counitIso := {
    hom := {
      app s := (isoOfEq (perm_inv_perm π s)).hom
      naturality {s t} f := by
        apply DFunLike.coe_injective
        ext x
        change π ⬝ π⁻¹ ⬝ f _ = (f _).val
        rw [perm_inv_perm]
        congr 2
        simp only [perm_val, permIso, inv_inv, finInjPermFunctor, Embedding.coeFn_mk,
          Finperm.apply_inv_self, comp_obj, id_obj, isoOfEq]
    }
    inv := {
      app s := (isoOfEq (perm_inv_perm π s)).inv
      naturality {s t} f := by
        apply DFunLike.coe_injective
        ext x
        change (f _).val = π ⬝ π⁻¹ ⬝ f _
        rw [perm_inv_perm]
        congr
        simp only [perm_val, permIso, inv_inv, finInjPermFunctor, id_obj, comp_obj, isoOfEq,
          Embedding.coeFn_mk, Finperm.apply_inv_self, Subtype.coe_eta]
    }
  }
  functor_unitIso_comp s := by
    apply DFunLike.coe_injective
    ext x : 2
    simp only [finInjPermFunctor, permIso, perm_val, id_obj, comp_obj, isoOfEq, Category.assoc]
    exact perm_inv_perm π _
