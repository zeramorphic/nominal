import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.Data.Finite.Sum

/-!
# The category of finite sets and injections

This small category is not filtered, but has a cocone for every span.
Fortunately, this is enough to make the usual construction of filtered colimits work.
-/

open CategoryTheory Functor Limits Finset

@[ext]
structure FinInj (α : Type*) where
  val : Finset α

attribute [coe] FinInj.val

instance {α : Type*} : Category (FinInj α) where
  Hom s t := {f : s.val → t.val // Function.Injective f}
  id s := ⟨id, λ _ _ ↦ id⟩
  comp f g := ⟨g.val ∘ f.val, g.prop.comp f.prop⟩

instance {α : Type*} : Nonempty (FinInj α) :=
  ⟨⟨∅⟩⟩

inductive FinInj.SpanCoconeApex {α : Type*} [DecidableEq α]
    (F : WalkingSpan ⥤ FinInj α) where
  | inl : (F.obj (some .left)).val → FinInj.SpanCoconeApex F
  | inr' : (y : (F.obj (some .right)).val) → (∀ x, y ≠ (F.map (.init .right)).val x) →
      FinInj.SpanCoconeApex F

noncomputable def FinInj.SpanCoconeApex.inr {α : Type*} [DecidableEq α]
    {F : WalkingSpan ⥤ FinInj α} (y : (F.obj (some .right)).val) : FinInj.SpanCoconeApex F :=
  if h : ∃ x, y = (F.map (.init .right)).val x then
    .inl ((F.map (.init .left)).val h.choose)
  else
    .inr' y (by push_neg at h; exact h)

theorem FinInj.SpanCoconeApex.inr_injective {α : Type*} [DecidableEq α]
    {F : WalkingSpan ⥤ FinInj α} :
    Function.Injective (.inr : (F.obj (some .right)).val → FinInj.SpanCoconeApex F) := by
  intro x y h
  rw [inr, inr] at h
  split_ifs at h with h₁ h₂
  case pos =>
    rw [inl.injEq, (F.map (.init .left)).prop.eq_iff] at h
    rw [h₁.choose_spec, h₂.choose_spec, h]
  case neg =>
    cases h
    rfl

theorem FinInj.SpanCoconeApex.inl_eq_inr {α : Type*} [DecidableEq α]
    {F : WalkingSpan ⥤ FinInj α} (x : (F.obj none).val) :
    SpanCoconeApex.inl ((F.map (.init .left)).val x) =
      SpanCoconeApex.inr ((F.map (.init .right)).val x) := by
  have : ∃ y, (F.map (.init .right)).val x = (F.map (.init .right)).val y := ⟨x, rfl⟩
  rw [inr, dif_pos this, inl.injEq, (F.map (.init .left)).prop.eq_iff]
  exact (F.map (.init .right)).prop this.choose_spec

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
      | none => ⟨λ x ↦ equivOfFinite (.inl ((F.map (.init .left)).val x)), by
          intro x y h
          simp only [const_obj_obj, EmbeddingLike.apply_eq_iff_eq, SpanCoconeApex.inl.injEq] at h
          exact (F.map (.init .left)).prop h⟩
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
      apply Subtype.val_injective
      cases f
      case a.id =>
        simp only [const_obj_obj, WidePushoutShape.hom_id, CategoryTheory.Functor.map_id,
          Category.id_comp, const_obj_map, Category.comp_id]
      case a.init i =>
        cases i
        case left => rfl
        case right =>
          ext x
          simp only [const_obj_obj, CategoryStruct.comp, Function.comp_apply, const_obj_map,
            CategoryStruct.id, SpanCoconeApex.inl_eq_inr, Function.id_comp]
  }
