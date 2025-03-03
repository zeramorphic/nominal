import Mathlib.CategoryTheory.Generator.Basic
import Nominal.Category.Coreflection

/-!
# Separators and coseparators

In this file, we exhibit separating and coseparating sets for the category of nominal sets.

Note that Nom has no single separating object. Suppse that `X` were such a separator.
Let `n` be the size of the smallest support of an object in `X`; note that `X` must be nonempty
otherwise it obviously fails to be a separator. Then let `Y` be the nominal set of finite sets
of atoms of size greater than `n`. Now, `Nom(X, Y)` is empty, because if `f : X → Y` were
equivariant, it would map `x` with support of size `n` to `f x` with support of size at most `n`,
so `|f x| <= n`, a contradiction.

However, Nom does have a single coseparator, namely, `FS 𝔸 (Power 𝔸 (Discrete (PUnit ⊕ PUnit)))`.
Indeed, because Nom is a coreflective subcategory of Set which has a coseparator
(namely the two-inhabitant type), we can obtain a coseparator for Nom by applying the coreflector.
-/

open CategoryTheory Functor

variable {𝔸 : Type*} [DecidableEq 𝔸]
