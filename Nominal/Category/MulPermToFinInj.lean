import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Nominal.Category.FinInj

/-!
# Functor from `MulPerm 𝔸` to `FinInj 𝔸 ⥤ Type`

In this file, we construct the functor
`mulPermToFinInj : Bundled (MulPerm 𝔸) ⥤ (FinInj 𝔸 ⥤ Type)`.
-/

open CategoryTheory Functor Limits

variable {𝔸 : Type*} [DecidableEq 𝔸]

@[ext]
structure SupportedBy (α : Type*) [HasPerm 𝔸 α] (s : Finset 𝔸) where
  val : α
  supports : Supports s val

noncomputable def SupportedBy.map {α : Type*} [MulPerm 𝔸 α]
    {s t : Finset 𝔸} (f : s → t) (hf : Function.Injective f)
    (x : SupportedBy α s) : SupportedBy α t where
  val := (Finperm.exists_extension' ⟨f, hf⟩).choose ⬝ x.val
  supports := by
    intro π hπ
    rw [← mul_perm]
    apply x.supports.perm_eq_perm
    intro a ha
    rw [Finperm.coe_mul, Function.comp_apply,
      (Finperm.exists_extension' ⟨f, hf⟩).choose_spec.1 a ha, hπ]
    exact Finset.coe_mem _

theorem SupportedBy.map_apply_eq_perm {α : Type*} [MulPerm 𝔸 α]
    {s t : Finset 𝔸} {f : s → t} {hf : Function.Injective f}
    (π : Finperm 𝔸) (hπ : ∀ x : s, f x = π x) (x : SupportedBy α s) :
    (map f hf x).val = π ⬝ x.val := by
  rw [map]
  apply x.supports.perm_eq_perm
  intro a ha
  rw [(Finperm.exists_extension' ⟨f, hf⟩).choose_spec.1 a ha]
  exact hπ ⟨a, ha⟩

theorem SupportedBy.map_id {α : Type*} [MulPerm 𝔸 α] (s : Finset 𝔸) :
    map (id : s → s) (λ _ _ ↦ id) = (id : SupportedBy α s → SupportedBy α s) := by
  ext x
  rw [map_apply_eq_perm 1]
  · simp only [one_perm, id_eq]
  · simp only [id_eq, Finperm.coe_one, implies_true]

theorem SupportedBy.map_comp {α : Type*} [MulPerm 𝔸 α] {s t u: Finset 𝔸}
    (f : s → t) (hf : Function.Injective f) (g : t → u) (hg : Function.Injective g) :
    map (g ∘ f) (hg.comp hf) = (map g hg ∘ map f hf : SupportedBy α s → _) := by
  ext x
  obtain ⟨πf, hπf, -⟩ := Finperm.exists_extension' ⟨f, hf⟩
  obtain ⟨πg, hπg, -⟩ := Finperm.exists_extension' ⟨g, hg⟩
  rw [Function.comp_apply]
  rw [map_apply_eq_perm (f := g) πg, map_apply_eq_perm (f := f) πf,
    map_apply_eq_perm (πg * πf), mul_perm]
  · intro a
    simp only [Function.comp_apply, Finperm.coe_mul]
    rw [hπf, hπg]
    rfl
  · intro a
    exact (hπf a a.prop).symm
  · intro a
    exact (hπg a a.prop).symm

noncomputable def supportedBy.{u} (α : Type u) [MulPerm 𝔸 α] : FinInj 𝔸 ⥤ Type u where
  obj s := SupportedBy α s.val
  map f := SupportedBy.map f f.injective
  map_id s := SupportedBy.map_id s.val
  map_comp f g := SupportedBy.map_comp f f.injective g g.injective

noncomputable def mulPermToFinInj : Bundled (MulPerm 𝔸) ⥤ (FinInj 𝔸 ⥤ Type*) where
  obj α := supportedBy α
  map := sorry
  map_id := sorry
  map_comp := sorry
