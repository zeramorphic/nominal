import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Nominal.Instances

/-!
# The category of nominal sets

In this file, we translate our nominal definitions into the language of mathlib's
category theory library. This allows us to appeal to results such as the adjoint
functor theorem.

It is difficult to use these results directly because they are stated in bundled form
(objects are types-with-structure not types together with typeclass-inferred structure),
whereas the rest of this nominal sets library uses unbundled form.
-/

open CategoryTheory

variable {𝔸 : Type*} [DecidableEq 𝔸]

instance : Category (Bundled (Nominal 𝔸)) where
  Hom α β := {f : α → β // Equivariant 𝔸 f}
  id := sorry
  comp := sorry
