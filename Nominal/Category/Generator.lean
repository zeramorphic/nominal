import Mathlib.CategoryTheory.Generator.Basic
import Nominal.Category.Coreflection
import Nominal.Category.Forget

/-!
# Separators and coseparators

In this file, we exhibit separating and coseparating sets for the category of nominal sets.

Note that Nom has no single separating object. Suppse that `X` were such a separator.
Let `n` be the size of the smallest support of an object in `X`; note that `X` must be nonempty
otherwise it obviously fails to be a separator. Then let `Y` be the nominal set of finite sets
of atoms of size greater than `n`. Now, `Nom(X, Y)` is empty, because if `f : X → Y` were
equivariant, it would map `x` with support of size `n` to `f x` with support of size at most `n`,
so `|f x| <= n`, a contradiction. So `X` cannot separate maps with domain `Y`.

However, Nom does have a single coseparator, namely, `FS 𝔸 (Power 𝔸 (ULift Prop))`.
This follows from the general fact that given an adjunction `F : C ⥤ D ⊣ G : D ⥤ C`
where the left adjoint is faithful, any coseparating set in `D` can be converted into a
coseparating set in `C`.
-/

open CategoryTheory Functor

universe u

variable {𝔸 : Type u} [DecidableEq 𝔸]

/-- Given an adjunction `F : C ⥤ D ⊣ G : D ⥤ C` where the left adjoint is faithful,
any coseparating set in `D` can be converted into a coseparating set in `C`. -/
theorem CategoryTheory.Adjunction.isCoseparating_of_faithful
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (hf : F.Faithful) {s : Set D} (hs : IsCoseparating s) :
    IsCoseparating (G.obj '' s) := by
  intro X Y f g h
  apply hf.map_injective
  apply hs
  intro Z hZ p
  have := h _ ⟨Z, hZ, rfl⟩ (adj.homEquiv Y Z p)
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_left,
    EquivLike.apply_eq_iff_eq] at this
  exact this

/-- If `F ⊣ G` where the left adjoint is faithful, then any coseparator in `D`
can be converted to a coseparator in `C`. -/
theorem CategoryTheory.Adjunction.isCoseparator_of_faithful
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (hf : F.Faithful) {X : D} (hs : IsCoseparator X) :
    IsCoseparator (G.obj X) := by
  have := adj.isCoseparating_of_faithful hf hs
  rwa [Set.image_singleton] at this

theorem CategoryTheory.Types.prop_isCoseparator.{v} :
    IsCoseparator (ULift.{v} Prop) := by
  intro α β f g h
  ext x
  have := congr_arg (· x) (h _ rfl (λ y ↦ .up (f x = y)))
  simp only [types_comp_apply, ULift.up.injEq, eq_iff_iff, true_iff] at this
  exact this

theorem Nominal.prop_isCoseparator.{v} :
    IsCoseparator ((MulPerm.power 𝔸 ⋙ nominalCoreflection 𝔸).obj (ULift.{max u v} Prop)) :=
  (forgetAdj 𝔸).isCoseparator_of_faithful (HasForget.forget_faithful) (Types.prop_isCoseparator)

instance Nominal.hasCoseparator.{v} : HasCoseparator (Bundled.{max u v} (Nominal 𝔸)) :=
  ⟨_, Nominal.prop_isCoseparator⟩
