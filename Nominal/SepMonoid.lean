import Nominal.Abstraction
import Nominal.SepProd

open Finperm Rel SepProd

/-!
# Separated monoids

We define *separated monoids*, which are monoid objects internal to the monoidal category where

* the objects are nominal sets;
* the morphisms are strong equivariant maps (which are support-preserving functions);
* the monoid is separating conjunction.

Examples of separated monoids include the unit and empty types, finite sets of names,
and finite lists of names.

Our key theorem is that if `α` is a separated monoid, then the functor `[α|𝔸](-)` becomes a monad.
-/

@[ext]
class SepMul (𝔸 : Type*) [DecidableEq 𝔸] (α : Type*) [MulPerm 𝔸 α] where
  sepMul : α ∗[𝔸] α → α
  sepMul_equivariant : Equivariant 𝔸 sepMul
  sepMul_strong : StrongMap 𝔸 sepMul

export SepMul (sepMul)

/-- The morphism `Unit → α` given by `sepUnit` is automatically strong. -/
@[ext]
class SepUnit (𝔸 : Type*) [DecidableEq 𝔸] (α : Type*) [HasPerm 𝔸 α] where
  sepUnit : α
  sepUnit_equivariant : Equivariant 𝔸 sepUnit

export SepUnit (sepUnit)

/-- A typeclass for *separated monoids*, which are the internal monoids to the monoidal category
`(Nom, ∗[𝔸])`. -/
class SepMonoid (𝔸 : Type*) [DecidableEq 𝔸] [Infinite 𝔸] (α : Type*) [Nominal 𝔸 α]
    extends SepMul 𝔸 α, SepUnit 𝔸 α where
  sepUnit_sepMul (x : α) : sepMul (leftInj sepUnit sepUnit_equivariant x) = x
  sepMul_sepUnit (x : α) : sepMul (rightInj sepUnit sepUnit_equivariant x) = x
  sepMul_assoc (x : (α ∗[𝔸] α) ∗[𝔸] α) :
    sepMul (x.first sepMul sepMul_equivariant) =
    sepMul ((assoc α α α x).second sepMul sepMul_equivariant)

instance {𝔸 : Type*} [DecidableEq 𝔸] [Infinite 𝔸] {α : Type*} [DecidableEq α] [Nominal 𝔸 α] :
    SepMonoid 𝔸 (Finset α) where
  sepMul x := x.fst ∪ x.snd
  sepMul_equivariant := by
    intro π
    ext x a
    simp only [Function.perm_def, perm_fst, perm_snd, Finset.mem_perm, Finset.mem_union,
      _root_.inv_inv, perm_inv_perm]
  sepMul_strong := by
    apply strongMap_of_supp_eq_supp
    intro x
    ext a
    simp only [Finset.supp_eq, supp_eq]
    aesop
  sepUnit := ∅
  sepUnit_equivariant := by intro; rfl
  sepUnit_sepMul x := by simp only [leftInj, Finset.empty_union]
  sepMul_sepUnit x := by simp only [rightInj, leftInj, symm_fst, symm_snd, Finset.union_empty]
  sepMul_assoc x := by simp only [first_fst, first_snd, Finset.union_assoc, assoc, Equiv.coe_fn_mk,
    assoc', second_fst, second_snd]

/-!
# Generalised abstraction monad

If `α` is a separated monoid, then the functor `[α|𝔸](-)` becomes a monad.
-/

namespace Abstract

variable {𝔸 α β γ : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
  [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]

theorem sepMap_aux (x₁ x₂ : α ∗[𝔸] β) (z₁ z₂ : γ)
    (h : (⟨x₁, z₁⟩ : Abstract' 𝔸 (α ∗[𝔸] β) γ).Rel ⟨x₂, z₂⟩) :
    (⟨x₁.fst⟩(⟨x₁.snd⟩z₁) : [α|𝔸][β|𝔸]γ) = ⟨x₂.fst⟩(⟨x₂.snd⟩z₂) := by
  obtain ⟨π, hπ₁, hπ₂⟩ := h
  cases hπ₁
  rw [mk_eq_iff]
  refine ⟨π, rfl, ?_⟩
  rw [Finperm.fresh_iff] at hπ₂ ⊢
  intro a ha
  apply hπ₂
  simp only [Abstract.supp_eq, Finset.names_supp_eq, Finset.mem_sdiff, supp_eq, Finset.mem_union,
    not_or] at ha ⊢
  tauto

def sepMap : [α ∗[𝔸] β | 𝔸]γ → [α|𝔸][β|𝔸]γ :=
  lift (λ x z ↦ ⟨x.fst⟩(⟨x.snd⟩z)) sepMap_aux

theorem sepMap_injective : Function.Injective (sepMap : [α ∗[𝔸] β | 𝔸]γ → [α|𝔸][β|𝔸]γ) := by
  intro x₁ x₂ h
  induction x₁ using ind
  case mk x₁ y₁ =>
  induction x₂ using ind
  case mk x₂ y₂ =>
  rw [sepMap, lift_mk, lift_mk, mk_eq_iff, Abstract'.rel_iff] at h
  obtain ⟨π, hπ₁, hπ₂, hπ₃⟩ := h
  rw [Abstract'.perm_def, perm_mk, Abstract'.mk.injEq, mk_eq_iff, Abstract'.rel_iff] at hπ₁
  obtain ⟨hπ₁, π', hπ'₁, hπ'₂, hπ'₃⟩ := hπ₁
  simp only [Abstract'.perm_def, Abstract'.mk.injEq] at hπ'₁
  simp only [Abstract.supp_eq, supp_perm_eq] at hπ₂ hπ'₂
  rw [mk_eq_iff]
  refine ⟨π' * π, ?_, ?_⟩
  · simp only [Abstract'.perm_def, Abstract'.mk.injEq, mul_perm]
    refine ⟨?_, hπ'₁.2⟩
    ext
    · rw [perm_fst, perm_fst, perm_eq_of_fresh, hπ₁]
      rw [Finperm.fresh_iff]
      intro a ha
      by_contra ha'
      rw [← ne_eq, ← Finperm.mem_support_iff] at ha'
      specialize hπ'₃ ha'
      simp only [supp_perm_eq, Finset.mem_union] at hπ'₃
      obtain h | h := hπ'₃
      · rw [supp_perm_eq, Finset.mem_perm] at ha
        rw [Finset.mem_perm] at h
        have := x₁.sep
        rw [fresh_def, Finset.disjoint_iff_ne] at this
        exact this _ ha _ h rfl
      · dsimp only at hπ₁
        rw [hπ₁] at ha
        have := x₂.sep
        rw [fresh_def, Finset.disjoint_iff_ne] at this
        exact this _ ha _ h rfl
    · exact hπ'₁.1
  · rw [fresh_iff] at hπ₂ hπ'₂ ⊢
    intro a ha
    simp only [supp_eq, Finset.names_supp_eq, Finset.mem_sdiff, Finset.mem_union, not_or] at ha
    have hπa : π a = a := by
      apply hπ₂
      simp only [Finset.names_supp_eq, Finset.mem_sdiff]
      tauto
    have hπa' : π' a = a := by
      apply hπ'₂
      symm at hπa
      rw [← inv_apply_eq_iff_eq] at hπa
      simp only [Finset.names_supp_eq, Finset.mem_sdiff, Finset.mem_perm, perm_name_eq, hπa]
      tauto
    rw [mul_apply, hπa, hπa']

theorem sepMap_surjective : Function.Surjective (sepMap : [α ∗[𝔸] β | 𝔸]γ → [α|𝔸][β|𝔸]γ) := by
  intro x
  induction x using ind
  case mk x y =>
  induction y using fresh_induction x
  infer_instance
  case h y z h =>
  use ⟨⟨x, y, h.symm⟩⟩z
  rfl

/-- The equivariant equivalence between `[α ∗[𝔸] β | 𝔸]γ` and `[α|𝔸][β|𝔸]γ`. -/
noncomputable def sepEquiv : [α ∗[𝔸] β | 𝔸]γ ≃ [α|𝔸][β|𝔸]γ :=
  Equiv.ofBijective sepMap ⟨sepMap_injective, sepMap_surjective⟩

theorem sepEquiv_mk_symm (x : α) (y : β) (z : γ) (h : x #[𝔸] y) :
    sepEquiv.symm (⟨x⟩(⟨y⟩z)) = ⟨⟨x, y, h⟩⟩z := by
  rw [Equiv.symm_apply_eq]
  rfl

/-!
We now define the monad structure on `[α|𝔸]β` under the assumption that `α` has a
separated monoid structure.
-/

def pure [SepMonoid 𝔸 α] (x : β) : [α|𝔸]β :=
  ⟨sepUnit 𝔸⟩x

theorem pure_equivariant [SepMonoid 𝔸 α] : Equivariant 𝔸 (pure : β → [α|𝔸]β) := by
  intro π
  ext x
  simp only [Function.perm_def, pure, perm_mk, perm_inv_perm]
  rw [SepUnit.sepUnit_equivariant]

/-- The monadic multiplication. -/
noncomputable def mul [SepMonoid 𝔸 α] : [α|𝔸][α|𝔸]β → [α|𝔸]β :=
  Abstract.amap sepMul SepMul.sepMul_equivariant SepMul.sepMul_strong ∘ sepEquiv.symm

theorem mul_mk_eq [SepMonoid 𝔸 α] (x y : α) (h : y #[𝔸] x) (z : β) :
    (mul (⟨x⟩(⟨y⟩z)) : [α|𝔸]β) = ⟨sepMul ⟨x, y, h.comm⟩⟩z := by
  rw [mul, Function.comp_apply, sepEquiv_mk_symm]
  rfl

theorem mul_equivariant [SepMonoid 𝔸 α] : Equivariant 𝔸 (mul : [α|𝔸][α|𝔸]β → [α|𝔸]β) := by
  intro π
  ext x
  induction x using ind
  case mk x y =>
  induction y using fresh_induction x
  infer_instance
  case h y z h =>
  rw [Function.perm_def, perm_mk, perm_mk, mul_mk_eq x y h, mul_mk_eq _ _ (h.perm π⁻¹)]
  simp only [perm_mk, apply_perm_eq SepMul.sepMul_equivariant, SepProd.perm_def, perm_inv_perm]

/-! We now prove the monad laws. -/

theorem left_unit [SepMonoid 𝔸 α] (x : [α|𝔸]β) :
    mul (pure x) = x := by
  induction x using ind
  case mk x y =>
  rw [pure, mul_mk_eq]
  · have := SepMonoid.sepUnit_sepMul (𝔸 := 𝔸) x
    rw [leftInj] at this
    rw [this]
  · rw [fresh_def, SepUnit.sepUnit_equivariant.supp_eq_empty]
    exact λ _ _ ↦ id

theorem right_unit [SepMonoid 𝔸 α] (x : [α|𝔸]β) :
    mul (x.map pure pure_equivariant.finitelySupported) = x := by
  induction x using ind
  case mk x y =>
  rw [map_mk]
  · rw [pure, mul_mk_eq]
    · congr 1
      exact SepMonoid.sepMul_sepUnit (𝔸 := 𝔸) x
    · rw [fresh_def, SepUnit.sepUnit_equivariant.supp_eq_empty]
      exact λ _ a _ ↦ a
  · rw [fresh_def, (pure_equivariant (𝔸 := 𝔸) (α := α) (β := β)).supp_eq_empty]
    exact λ _ _ ↦ id

theorem assoc [SepMonoid 𝔸 α] (x : [α|𝔸][α|𝔸][α|𝔸]β) :
    mul (x.map mul mul_equivariant.finitelySupported) = mul (mul x) := by
  induction x using ind
  case mk x₁ y =>
  induction y using fresh_induction x₁
  infer_instance
  case h x₂ y h₁ =>
  induction y using fresh_induction (x₁, x₂)
  infer_instance
  case h x₃ y h₂ =>
  simp only [Prod.fresh_iff] at h₂
  rw [map_mk, mul_mk_eq _ _ h₂.2, mul_mk_eq, mul_mk_eq _ _ h₁, mul_mk_eq]
  · have := SepMonoid.sepMul_assoc (𝔸 := 𝔸) ⟨⟨x₁, x₂, h₁.comm⟩, x₃, ?_⟩
    swap
    · rw [fresh_def, SepProd.supp_eq, Finset.disjoint_union_left, ← fresh_def, ← fresh_def]
      exact ⟨h₂.1.comm, h₂.2.comm⟩
    congr 1
    exact this.symm
  · rw [fresh_def, SepMul.sepMul_strong.supp_eq SepMul.sepMul_equivariant,
      supp_eq, Finset.disjoint_union_right, ← fresh_def, ← fresh_def]
    exact h₂
  · rw [fresh_def, SepMul.sepMul_strong.supp_eq SepMul.sepMul_equivariant,
      supp_eq, Finset.disjoint_union_left, ← fresh_def, ← fresh_def]
    exact ⟨h₁, h₂.1⟩
  · rw [fresh_def, mul_equivariant.supp_eq_empty]
    exact λ _ _ ↦ id

end Abstract
