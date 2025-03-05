import Nominal.Category.FinInj

/-!
# Expanding sets of names

Given an injection `i : α ↪ β`, we get an equivalence of categories `FinInj α ⥤ FinInj β`.
-/

open CategoryTheory Functor Finset

variable {α β : Type*}

/-- We'll define an injection `α → β` to consist of a map `α → β` as well as a left inverse
on its image. This allows for better definitional equalities in the functors we will define. -/
structure Injection (α β : Type*) where
  toFun : α → β
  invFun : Set.range toFun → α
  leftInv : ∀ x, invFun ⟨toFun x, x, rfl⟩ = x

theorem Injection.toFun_injective (i : Injection α β) :
    Function.Injective i.toFun := by
  intro x y h
  rw [← i.leftInv x, ← i.leftInv y]
  congr

theorem Injection.invFun_injective (i : Injection α β) :
    Function.Injective i.invFun := by
  rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩ h
  rw [leftInv, leftInv] at h
  rw [h]

def Injection.inj (i : Injection α β) : α ↪ β where
  toFun := i.toFun
  inj' := i.toFun_injective

instance : FunLike (Injection α β) α β where
  coe := Injection.toFun
  coe_injective' := by
    rintro ⟨f₁, g₁, h₁⟩ ⟨f₂, g₂, h₂⟩ rfl
    simp only [Injection.mk.injEq, heq_eq_eq, true_and]
    ext x
    obtain ⟨_, x, rfl⟩ := x
    rw [h₁, h₂]

@[simp]
theorem Injection.coe_apply_inj {i : Injection α β} (x y : α) :
    i x = i y ↔ x = y :=
  i.inj.apply_eq_iff_eq x y

@[simp]
theorem Injection.invFun_apply_inj {i : Injection α β} (x y : Set.range i) :
    i.invFun x = i.invFun y ↔ x = y :=
  i.invFun_injective.eq_iff

@[simp]
theorem Injection.invFun_apply {i : Injection α β} (x : α) :
    i.invFun ⟨i x, x, rfl⟩ = x :=
  i.leftInv x

@[simp]
theorem Injection.apply_invFun {i : Injection α β} (x : Set.range i) :
    i (i.invFun x) = x := by
  obtain ⟨_, x, rfl⟩ := x
  rw [invFun_apply]

def expandNamesObj (i : Injection α β) (s : FinInj α) : FinInj β :=
  ⟨s.val.map i.inj⟩

def expandNamesEquiv (i : Injection α β) (s : FinInj α) :
    s.val ≃ (expandNamesObj i s).val where
  toFun x := ⟨i x, by
    simp only [expandNamesObj, mem_map]
    exact ⟨x, x.prop, rfl⟩⟩
  invFun x := ⟨i.invFun ⟨x,
    by
      have := x.prop
      simp only [expandNamesObj, mem_map] at this
      obtain ⟨y, hy, hy'⟩ := this
      exact ⟨y, hy'⟩⟩,
    by
      have := x.prop
      simp only [expandNamesObj, mem_map] at this
      obtain ⟨y, hy, hy'⟩ := this
      rw [← i.leftInv y] at hy
      convert hy
      exact hy'.symm⟩
  left_inv x := by
    simp only [Injection.invFun_apply, Subtype.coe_eta]
  right_inv x := by
    simp only [Injection.apply_invFun, Subtype.coe_eta]

theorem symm_toEmbedding_trans_eq_iff {α β γ : Type*} (e : β ≃ α) (f : β ↪ γ) (g : α ↪ γ) :
    e.symm.toEmbedding.trans f = g ↔ f = e.toEmbedding.trans g := by
  constructor
  · rintro rfl
    ext x
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  · rintro rfl
    ext x
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.apply_symm_apply]

theorem Function.Embedding.trans_assoc {α β γ δ : Type*} (e : α ↪ β) (f : β ↪ γ) (g : γ ↪ δ) :
    (e.trans f).trans g = e.trans (f.trans g) :=
  rfl

/-- Given an injection `i : α ↪ β`, we obtain a functor `FinInj α ⥤ FinInj β`, defined on objects
by mapping along `i`. -/
def expandNames (i : Injection α β) : FinInj α ⥤ FinInj β where
  obj s := ⟨s.val.map i.inj⟩
  map {s t} f := (expandNamesEquiv i s).symm.toEmbedding.trans
    (f.trans (expandNamesEquiv i t).toEmbedding)
  map_id s := by
    rw [symm_toEmbedding_trans_eq_iff]
    rfl
  map_comp {s t u} f g := by
    dsimp only [CategoryStruct.comp]
    conv_rhs => {
      rw [Function.Embedding.trans_assoc, Function.Embedding.trans_assoc,
        ← Function.Embedding.trans_assoc
          ((expandNamesEquiv i t).toEmbedding) ((expandNamesEquiv i t).symm.toEmbedding),
        Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding]
    }
    rfl

def expandNames_fullyFaithful (i : Injection α β) :
    FullyFaithful (expandNames i) where
  preimage {s t} f := ((expandNamesEquiv i s).toEmbedding.trans f).trans
    (expandNamesEquiv i t).symm.toEmbedding
  map_preimage {s t} f := by
    simp only [expandNames]
    rw [Function.Embedding.trans_assoc, Function.Embedding.trans_assoc,
      Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding,
      ← Function.Embedding.trans_assoc,
      Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding]
    rfl
  preimage_map f := by
    simp only [expandNames]
    rw [← Function.Embedding.trans_assoc, ← Function.Embedding.trans_assoc,
      Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding,
      Function.Embedding.trans_assoc,
      Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding]
    rfl

instance expandNames_full (i : Injection α β) :
    Full (expandNames i) :=
  (expandNames_fullyFaithful i).full

instance expandNames_faithful (i : Injection α β) :
    Faithful (expandNames i) :=
  (expandNames_fullyFaithful i).faithful

instance expandNames_essSurj [Infinite α] (i : Injection α β) :
    EssSurj (expandNames i) := by
  constructor
  intro t
  obtain ⟨⟨s, e⟩⟩ := Finset.exists_equiv_of_finite α t.val
  exact ⟨⟨s⟩,
    ⟨(e.trans (expandNamesEquiv i ⟨s⟩)).symm.toEmbedding,
      (e.trans (expandNamesEquiv i ⟨s⟩)).toEmbedding,
      Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding _,
      Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding _⟩⟩

instance expandNames_isEquivalence [Infinite α] (i : Injection α β) :
    IsEquivalence (expandNames i) where

def expandNamesPre [Infinite α] (i : Injection α β) :
    (FinInj β ⥤ Type*) ⥤ (FinInj α ⥤ Type _) :=
  (whiskeringLeft _ _ _).obj (expandNames i)

instance expandNamesPre_isEquivalence [Infinite α] (i : Injection α β) :
    IsEquivalence (expandNamesPre i) :=
  inferInstanceAs (IsEquivalence ((whiskeringLeft _ _ _).obj _))
