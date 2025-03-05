import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.Data.Finite.Sum
import Mathlib.Logic.Embedding.Basic

/-!
# The category of finite sets and injections

This small category is not filtered, but has a cocone for every span.
Fortunately, this is enough to make the usual construction of filtered colimits work.
-/

open CategoryTheory Function Functor Limits Finset

@[ext]
structure FinInj (α : Type*) where
  val : Finset α

attribute [coe] FinInj.val

instance {α : Type*} : Category (FinInj α) where
  Hom s t := s.val ↪ t.val
  id s := Embedding.refl s.val
  comp := Embedding.trans

instance {α : Type*} {s t : FinInj α} :
    FunLike (s ⟶ t) s.val t.val :=
  inferInstanceAs (FunLike (s.val ↪ t.val) s.val t.val)

@[simp]
theorem FinInj.id_coe {α : Type*} (s : FinInj α) :
    ((𝟙 s : s ⟶ s) : s.val → s.val) = id :=
  rfl

@[simp]
theorem FinInj.comp_coe {α : Type*} {s t u : FinInj α} (f : s ⟶ t) (g : t ⟶ u) :
    ((f ≫ g) : s.val → u.val) = g ∘ f :=
  rfl

@[simp]
theorem FinInj.apply_eq_iff_eq {α : Type*} {s t : FinInj α} {f : s ⟶ t} (x y : s.val) :
    f x = f y ↔ x = y :=
  f.apply_eq_iff_eq x y

@[simp]
theorem FinInj.mk_coe_eq {α : Type*} {s t : FinInj α}
    (f : s.val → t.val) (h : Function.Injective f) :
    ((⟨f, h⟩ : s ⟶ t) : s.val → t.val) = f :=
  rfl

@[simp]
theorem FinInj.mk_apply_eq {α : Type*} {s t : FinInj α}
    (f : s.val → t.val) (h : Function.Injective f) (x : s.val) :
    (⟨f, h⟩ : s ⟶ t) x = f x :=
  rfl

instance {α : Type*} : Nonempty (FinInj α) :=
  ⟨⟨∅⟩⟩

/-!
## Pullbacks
-/

def FinInj.pullbackConeApex {α : Type*} [DecidableEq α] [Infinite α]
    (F : WalkingCospan ⥤ FinInj α) :
    FinInj α :=
  ⟨((F.obj (some .left)).val.attach.filter
    (λ x ↦ ∃ y, F.map (.term .left) x = F.map (.term .right) y)).map
    (Embedding.subtype _)⟩

def FinInj.pullbackConeMapNone {α : Type*} [DecidableEq α] [Infinite α]
    (F : WalkingCospan ⥤ FinInj α) :
    pullbackConeApex F ⟶ F.obj none where
  toFun x := ⟨F.map (.term .left) ⟨x,
    by
      have := x.prop
      simp only [pullbackConeApex, Subtype.exists, mem_map, mem_filter, mem_attach, true_and,
        Embedding.coe_subtype, exists_and_right, exists_eq_right] at this
      obtain ⟨hx, y, hy, h⟩ := this
      exact hx⟩,
    Finset.coe_mem _⟩
  inj' := by
    rintro ⟨y, hy⟩ ⟨z, hz⟩ h
    simp only [pullbackConeApex, Subtype.exists, mem_map, mem_filter, mem_attach, true_and,
        Embedding.coe_subtype, exists_and_right, exists_eq_right] at hy hz
    simp only [Subtype.mk.injEq] at h
    obtain ⟨hy, a, ha, hay⟩ := hy
    obtain ⟨hz, b, hb, hbz⟩ := hz
    rw [hay, hbz] at h
    have := (F.map (.term .right)).injective (Subtype.coe_injective h)
    rw [Subtype.mk.injEq] at this
    cases this
    rw [← hbz] at hay
    have := (F.map (.term .left)).injective hay
    rw [Subtype.mk.injEq] at this
    cases this
    rfl

def FinInj.pullbackConeMapLeft {α : Type*} [DecidableEq α] [Infinite α]
    (F : WalkingCospan ⥤ FinInj α) :
    pullbackConeApex F ⟶ F.obj (some .left) where
  toFun x := ⟨x,
    by
      have := x.prop
      simp only [pullbackConeApex, Subtype.exists, mem_map, mem_filter, mem_attach, true_and,
        Embedding.coe_subtype, exists_and_right, exists_eq_right] at this
      obtain ⟨hx, y, hy, h⟩ := this
      exact hx⟩
  inj' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp only [pullbackConeApex, Subtype.exists, mem_map, mem_filter, mem_attach, true_and,
      Embedding.coe_subtype, exists_and_right, exists_eq_right] at hx hy
    simp only [Subtype.mk.injEq] at h
    cases h
    rfl

def FinInj.pullbackConeMapRight' {α : Type*} [DecidableEq α] [Infinite α]
    (F : WalkingCospan ⥤ FinInj α) (x : (pullbackConeApex F).val) :
    (F.obj (some .right)).val :=
  (F.obj (some .right)).val.attach.choose
  (λ y ↦ F.map (.term .left) (pullbackConeMapLeft F x) = F.map (.term .right) y) <| by
    have := x.prop
    simp only [pullbackConeApex, Subtype.exists, mem_map, mem_filter, mem_attach, true_and,
      Embedding.coe_subtype, exists_and_right, exists_eq_right] at this
    obtain ⟨hx, y, hy, h⟩ := this
    refine ⟨⟨y, hy⟩, ⟨mem_attach _ _, h⟩, ?_⟩
    rintro ⟨z, hz⟩ ⟨hz', h'⟩
    exact (F.map (.term .right)).injective (h'.symm.trans h)

theorem FinInj.pullbackConeMapRight'_property {α : Type*} [DecidableEq α] [Infinite α]
    (F : WalkingCospan ⥤ FinInj α) (x : (pullbackConeApex F).val) :
    F.map (.term .left) (pullbackConeMapLeft F x) =
    F.map (.term .right) (pullbackConeMapRight' F x) :=
  (F.obj (some .right)).val.attach.choose_property
    (λ y ↦ F.map (.term .left) (pullbackConeMapLeft F x) = F.map (.term .right) y) _

def FinInj.pullbackConeMapRight {α : Type*} [DecidableEq α] [Infinite α]
    (F : WalkingCospan ⥤ FinInj α) :
    pullbackConeApex F ⟶ F.obj (some .right) where
  toFun := pullbackConeMapRight' F
  inj' := by
    intro x y h
    apply (pullbackConeMapLeft F).injective
    apply (F.map (.term .left)).injective
    apply (pullbackConeMapRight'_property F x).trans
    exact (h ▸ pullbackConeMapRight'_property F y).symm

theorem FinInj.pullbackConeMapRight_comp {α : Type*} [DecidableEq α] [Infinite α]
    (F : WalkingCospan ⥤ FinInj α) :
    pullbackConeMapRight F ≫ F.map (.term WalkingPair.right) = pullbackConeMapNone F := by
  apply DFunLike.coe_injective
  ext x : 1
  exact (pullbackConeMapRight'_property F x).symm

def FinInj.pullbackCone {α : Type*} [DecidableEq α] [Infinite α]
    (F : WalkingCospan ⥤ FinInj α) :
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

/-!
## Pushout cocones
-/

inductive FinInj.SpanCoconeApex {α : Type*} [DecidableEq α]
    (F : WalkingSpan ⥤ FinInj α) where
  | inl : (F.obj (some .left)).val → FinInj.SpanCoconeApex F
  | inr' : (y : (F.obj (some .right)).val) → (∀ x, y ≠ F.map (.init .right) x) →
      FinInj.SpanCoconeApex F

noncomputable def FinInj.SpanCoconeApex.inr {α : Type*} [DecidableEq α]
    {F : WalkingSpan ⥤ FinInj α} (y : (F.obj (some .right)).val) : FinInj.SpanCoconeApex F :=
  if h : ∃ x, y = F.map (.init .right) x then
    .inl (F.map (.init .left) h.choose)
  else
    .inr' y (by push_neg at h; exact h)

theorem FinInj.SpanCoconeApex.inr_injective {α : Type*} [DecidableEq α]
    {F : WalkingSpan ⥤ FinInj α} :
    Function.Injective (.inr : (F.obj (some .right)).val → FinInj.SpanCoconeApex F) := by
  intro x y h
  rw [inr, inr] at h
  split_ifs at h with h₁ h₂
  case pos =>
    rw [inl.injEq, apply_eq_iff_eq] at h
    rw [h₁.choose_spec, h₂.choose_spec, h]
  case neg =>
    cases h
    rfl

theorem FinInj.SpanCoconeApex.inl_eq_inr {α : Type*} [DecidableEq α]
    {F : WalkingSpan ⥤ FinInj α} (x : (F.obj none).val) :
    SpanCoconeApex.inl (F.map (.init .left) x) =
      SpanCoconeApex.inr (F.map (.init .right) x) := by
  have : ∃ y, F.map (.init .right) x = F.map (.init .right) y := ⟨x, rfl⟩
  rw [inr, dif_pos this, inl.injEq, apply_eq_iff_eq]
  exact (F.map (.init .right)).injective this.choose_spec

instance {α : Type*} [DecidableEq α] (F : WalkingSpan ⥤ FinInj α) :
    Finite (FinInj.SpanCoconeApex F) := by
  refine Finite.of_injective (β := (F.obj (some .left)).val ⊕ (F.obj (some .right)).val)
    (λ x ↦ match x with
      | .inl x => .inl x
      | .inr' x _ => .inr x) ?_
  intro x y h
  aesop

theorem Finset.exists_equiv_of_finite (α : Type*) [Infinite α] (β : Type*) [inst : Finite β] :
    Nonempty ((s : Finset α) × (β ≃ s)) := by
  rw [finite_iff_exists_equiv_fin] at inst
  obtain ⟨n, ⟨e⟩⟩ := inst
  obtain ⟨s, h⟩ := Infinite.exists_subset_card_eq α n
  exact ⟨⟨s, e.trans (s.equivFinOfCardEq h).symm⟩⟩

noncomputable def Finset.chosenOfFinite (α : Type*) [Infinite α] (β : Type*) [Finite β] :
    Finset α :=
  (exists_equiv_of_finite α β).some.fst

noncomputable def Finset.equivOfFinite {α : Type*} [Infinite α] {β : Type*} [Finite β] :
    β ≃ chosenOfFinite α β :=
  (exists_equiv_of_finite α β).some.snd

/--
This is not a colimiting cocone. Indeed, consider the other cocone `c` given by
```
∅   → {x}
↓      ↓
{x} → {x}
```
The map of apexes from this cocone to `c` is not injective, so this cocone is not colimiting.
-/
noncomputable def FinInj.pushoutCocone {α : Type*} [DecidableEq α] [Infinite α]
    (F : WalkingSpan ⥤ FinInj α) :
    Cocone F where
  pt := ⟨chosenOfFinite α (FinInj.SpanCoconeApex F)⟩
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
