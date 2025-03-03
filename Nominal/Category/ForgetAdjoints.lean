import Nominal.Category.Defs

/-!
# Adjoints to the forgetful functor

In this file, we produce adjoints to the forgetful functor `Bundled (MulPerm 𝔸) → Type _`.
As `Bundled (MulPerm 𝔸) ≌ (SingleObj (Finperm 𝔸) ⥤ Type _)` and `Type _ ≌ (Unit ⥤ Type _)`,
we can consider this forgetful functor to be given by pulling back along the unique functor
`SingleObj (Finperm 𝔸) ⥤ Unit`, and so its adjoints are given by the left and right Kan extensions.
More explicitly, the left adjoint is the `Finperm 𝔸`-copower, and the right adjoint is the
`Finperm 𝔸`-power.
-/

open CategoryTheory Functor Limits

namespace MulPerm

variable {𝔸 : Type*} [DecidableEq 𝔸]

@[ext]
structure Copower (𝔸 α : Type*) where
  π : Finperm 𝔸
  val : α

instance {α : Type*} : MulPerm 𝔸 (Copower 𝔸 α) where
  perm π x := ⟨π * x.π, x.val⟩
  one_perm x := by ext : 1; exact one_mul _; rfl
  mul_perm π₁ π₂ x := by ext : 1; exact mul_assoc _ _ _; rfl

theorem Copower.perm_def {α : Type*} (x : Copower 𝔸 α) (π : Finperm 𝔸) :
    π ⬝ x = ⟨π * x.π, x.val⟩ :=
  rfl

def copower.{u} (𝔸 : Type*) [DecidableEq 𝔸] : Type u ⥤ Bundled (MulPerm 𝔸) where
  obj α := ⟨Copower 𝔸 α, inferInstance⟩
  map f := ⟨λ x ↦ ⟨x.π, f x.val⟩, by
    intro π
    ext x : 1
    exact perm_inv_perm π (Copower.mk x.π (f x.val))⟩

def copowerAdj (𝔸 : Type*) [DecidableEq 𝔸] :
    copower 𝔸 ⊣ forget (Bundled (MulPerm 𝔸)) where
  unit := {
    app α x := ⟨1, x⟩
  }
  counit := {
    app α := ⟨λ x ↦ x.π ⬝ x.val, by
      intro π
      ext x
      change π ⬝ (π⁻¹ * x.π) ⬝ x.val = x.π ⬝ x.val
      rw [mul_perm, perm_inv_perm]⟩
    naturality α β f := by ext x; exact apply_perm_eq f.equivariant x.π x.val
  }
  left_triangle_components α := by
    ext x
    apply Copower.ext
    · exact mul_one _
    · rfl
  right_triangle_components α := by
    ext x
    exact one_perm _

@[ext]
structure Power (𝔸 α : Type*) where
  map : Finperm 𝔸 → α

instance {α : Type*} : HasPerm 𝔸 (Power 𝔸 α) where
  perm π x := ⟨λ π' ↦ x.map (π⁻¹ * π')⟩

@[simp]
theorem Power.perm_map {α : Type*} (x : Power 𝔸 α) (π π' : Finperm 𝔸) :
    (π ⬝ x).map π' = x.map (π⁻¹ * π') :=
  rfl

instance {α : Type*} : MulPerm 𝔸 (Power 𝔸 α) where
  one_perm x := by
    ext π'
    simp only [Power.perm_map, inv_one, one_mul]
  mul_perm π₁ π₂ x := by
    ext π'
    simp only [Power.perm_map, mul_inv_rev, mul_assoc]

def power.{u} (𝔸 : Type*) [DecidableEq 𝔸] : Type u ⥤ Bundled (MulPerm 𝔸) where
  obj α := ⟨Power 𝔸 α, inferInstance⟩
  map f := ⟨λ x ↦ ⟨λ π ↦ f (x.map π)⟩, _⟩

def powerAdj (𝔸 : Type*) [DecidableEq 𝔸] :
    forget (Bundled (MulPerm 𝔸)) ⊣ power 𝔸 where
  unit := {
    app α := ⟨λ x ↦ ⟨λ π ↦ π⁻¹ ⬝ x⟩, by
      intro π
      ext x
      apply Power.ext
      ext π'
      simp only [id_obj, comp_obj, Function.perm_def, Power.perm_map, mul_inv_rev, inv_inv,
        mul_perm, perm_inv_perm]⟩
    naturality α β f := by
      ext x
      apply Power.ext
      ext π
      exact apply_perm_eq f.equivariant π⁻¹ x
  }
  counit := {
    app α x := x.map 1
  }
  left_triangle_components α := by ext x; exact one_perm x
  right_triangle_components α := by
    ext x
    apply Power.ext
    ext π
    simp only [id_obj, power, CategoryStruct.comp, comp_obj, forget_hom, Function.comp_apply,
      Power.perm_map, inv_inv, mul_one, CategoryStruct.id, id]

end MulPerm
