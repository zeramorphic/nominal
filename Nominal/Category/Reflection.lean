import Nominal.Category.Coreflection
import Nominal.Category.FinInjColimit
import Nominal.Category.MulPermToFinInj

open CategoryTheory CategoryTheory.Functor

theorem finInjLeg_congr {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
    (s t : Finset 𝔸) {α : Bundled (Nominal 𝔸)}
    (x : SupportedBy α s) (y : SupportedBy α t)
    (hxy : x.val = y.val) :
    finInjLeg ⟨s⟩ x = (finInjLeg ⟨t⟩ y :
      ((nominalInclusion 𝔸 ⋙ mulPermToFinInj 𝔸) ⋙ finInjToNominal 𝔸).obj α) := by
  obtain ⟨x, hs⟩ := x
  obtain ⟨_, ht⟩ := y
  cases hxy
  have h₁ := finInjLeg_w ((nominalInclusion 𝔸 ⋙ mulPermToFinInj 𝔸).obj α)
    ((FinInj.unionCocone ⟨s⟩ ⟨t⟩).ι.app ⟨.left⟩)
  have h₂ := finInjLeg_w ((nominalInclusion 𝔸 ⋙ mulPermToFinInj 𝔸).obj α)
    ((FinInj.unionCocone ⟨s⟩ ⟨t⟩).ι.app ⟨.right⟩)
  simp only [comp_obj, Limits.pair_obj_left, Limits.pair_obj_right, const_obj_obj] at h₁ h₂
  rw [← h₁, ← h₂]
  clear h₁ h₂
  simp only [comp_obj, types_comp_apply]
  congr 1
  simp only [mulPermToFinInj, supportedBy, MulPerm.forget_hom, FinInj.unionCocone, const_obj_obj,
    Limits.pair_obj_left, Limits.pair_obj_right]
  ext : 1
  rw [SupportedBy.map_apply_eq_perm 1, SupportedBy.map_apply_eq_perm 1]
  · intro; rfl
  · intro; rfl

noncomputable def nominalReflection (𝔸 : Type*) [DecidableEq 𝔸] [Infinite 𝔸] :
    nominalInclusion 𝔸 ⋙ mulPermToFinInj 𝔸 ⊣ finInjToNominal 𝔸 where
  unit := {
    app α := {
      val x := finInjLeg ⟨supp 𝔸 x⟩ ⟨x, Nominal.supp_supports 𝔸 x⟩
      equivariant := by
        intro π
        funext x
        apply finInjLeg_congr
        simp only [comp_obj, id_obj, mulPermToFinInj, supportedBy]
        rw [SupportedBy.map_apply_eq_perm π]
        · exact perm_inv_perm _ _
        · intro
          rfl
    }
    naturality {s t} f := sorry
  }
  counit := sorry
  left_triangle_components := sorry
  right_triangle_components := sorry
