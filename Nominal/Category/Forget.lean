import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Nominal.Category.Limits

open CategoryTheory Functor Limits

variable {𝔸 : Type*} [DecidableEq 𝔸]

def Nominal.forget_pairCone_isLimit.{v} (K : Discrete WalkingPair ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit ((forget (Bundled.{v} (Nominal 𝔸))).mapCone (pairCone K)) where
  lift s x := ⟨s.π.app ⟨.left⟩ x, s.π.app ⟨.right⟩ x⟩
  fac s j := by
    obtain ⟨j | j⟩ := j
    case left => rfl
    case right => rfl
  uniq s m h := by
    ext x
    apply Prod.ext
    · exact congr_arg (· x) (h ⟨.left⟩)
    · exact congr_arg (· x) (h ⟨.right⟩)

instance Nominal.forget_preservesBinaryProducts.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] :
    PreservesLimitsOfShape (Discrete WalkingPair) (forget (Bundled.{v} (Nominal 𝔸))) :=
  ⟨λ {K} ↦ preservesLimit_of_preserves_limit_cone
    (Nominal.pairCone_isLimit K) (Nominal.forget_pairCone_isLimit K)⟩

def Nominal.forget_emptyCone_isLimit.{v} (K : Discrete PEmpty ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit ((forget (Bundled.{v} (Nominal 𝔸))).mapCone (emptyCone K)) where
  lift s _ := PUnit.unit

instance Nominal.forget_preservesEmpty.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] :
    PreservesLimitsOfShape (Discrete PEmpty) (forget (Bundled.{v} (Nominal 𝔸))) :=
  ⟨λ {K} ↦ preservesLimit_of_preserves_limit_cone
    (Nominal.emptyCone_isLimit K) (Nominal.forget_emptyCone_isLimit K)⟩

instance Nominal.forget_preservesFiniteProducts.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    PreservesFiniteProducts.{v} (forget (Bundled.{v} (Nominal 𝔸))) :=
  ⟨λ _ ↦ preservesShape_fin_of_preserves_binary_and_terminal _ _⟩

def Nominal.forget_equaliserCone_isLimit.{v} [Infinite 𝔸]
    (K : WalkingParallelPair ⥤ Bundled.{v} (Nominal 𝔸)) :
    IsLimit ((forget (Bundled.{v} (Nominal 𝔸))).mapCone (equaliserCone K)) where
  lift s x :=
    ⟨s.π.app .zero x, congr_arg (· x) ((s.π.naturality .left).symm.trans (s.π.naturality .right))⟩
  fac s j := by
    cases j
    case zero => rfl
    case one => exact s.w .left
  uniq s m h := by
    ext x
    have := congr_arg (· x) (h .zero)
    exact Equaliser.val_injective (hf := (K.map .left).prop) (hg := (K.map .right).prop) this

instance Nominal.forget_preservesEqualisers.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    PreservesLimitsOfShape WalkingParallelPair (forget (Bundled.{v} (Nominal 𝔸))) :=
  ⟨λ {K} ↦ preservesLimit_of_preserves_limit_cone
    (Nominal.equaliserCone_isLimit K) (Nominal.forget_equaliserCone_isLimit K)⟩

instance Nominal.forget_preservesFiniteLimits.{u, v} (𝔸 : Type u) [DecidableEq 𝔸] [Infinite 𝔸] :
    PreservesFiniteLimits.{v} (forget (Bundled (Nominal 𝔸))) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

theorem Nominal.mono_iff_injective [Infinite 𝔸] {α β : Bundled (Nominal 𝔸)} (f : α ⟶ β) :
    Mono f ↔ Function.Injective f :=
  ConcreteCategory.mono_iff_injective_of_preservesPullback f
