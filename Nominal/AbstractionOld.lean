import Nominal.Instances
import Nominal.Quantifier

open Finperm

variable {𝔸 α β : Type*} [DecidableEq 𝔸]

structure WithName (𝔸 : Type*) (α : Type*) where
  name : 𝔸
  val : α

namespace WithName

protected def rel [HasPerm 𝔸 α] (x y : WithName 𝔸 α) : Prop :=
  ν a, swap x.name a ⬝ x.val = swap y.name a ⬝ y.val

theorem rel_isEqv [HasPerm 𝔸 α] :
    Equivalence (WithName.rel : WithName 𝔸 α → WithName 𝔸 α → Prop) := by
  constructor
  · intro x
    rw [WithName.rel]
    simp only [newNames_true]
  · intro x y h
    apply h.mono
    intro a h'
    rw [h']
  · intro x y z h₁ h₂
    apply (h₁.and h₂).mono
    rintro a ⟨h₁', h₂'⟩
    rw [h₁', h₂']

protected instance setoid [HasPerm 𝔸 α] : Setoid (WithName 𝔸 α) where
  r := WithName.rel
  iseqv := rel_isEqv

end WithName

def Abstract (𝔸 : Type*) [DecidableEq 𝔸] (α : Type*) [HasPerm 𝔸 α] :=
  Quotient (WithName.setoid : Setoid (WithName 𝔸 α))

namespace Abstract

notation:max "["𝔸"]" α:max => Abstract 𝔸 α

def mk [HasPerm 𝔸 α] (a : 𝔸) (x : α) : [𝔸]α :=
  Quotient.mk WithName.setoid ⟨a, x⟩

notation "⟨"a"⟩" x:max => Abstract.mk a x

theorem sound [HasPerm 𝔸 α] {a b : 𝔸} {x y : α} (h : ν c, swap a c ⬝ x = swap b c ⬝ y) :
    ⟨a⟩x = ⟨b⟩y :=
  Quotient.sound h

def lift [HasPerm 𝔸 α] {β : Sort*} (f : 𝔸 → α → β)
    (hf : ∀ (a b : 𝔸) (x y : α), (ν c, swap a c ⬝ x = swap b c ⬝ y) → f a x = f b y) :
    [𝔸]α → β :=
  Quotient.lift (λ x ↦ f x.name x.val) (λ x y ↦ hf x.name y.name x.val y.val)

theorem ind [HasPerm 𝔸 α] {motive : [𝔸]α → Prop} (mk : ∀ a x, motive (⟨a⟩x)) :
    ∀ x, motive x :=
  Quotient.ind (λ x ↦ mk x.name x.val)

theorem exact [HasPerm 𝔸 α] {a b : 𝔸} {x y : α} (h : ⟨a⟩x = ⟨b⟩y) :
    ν c, swap a c ⬝ x = swap b c ⬝ y :=
  Quotient.exact h

theorem mk_eq_iff [HasPerm 𝔸 α] {a b : 𝔸} {x y : α} :
    ⟨a⟩x = ⟨b⟩y ↔ ν c, swap a c ⬝ x = swap b c ⬝ y :=
  ⟨exact, sound⟩

theorem swap_perm_eq_swap_perm_equivariant [MulPerm 𝔸 α] :
    Equivariant 𝔸 (λ c (x : 𝔸 × 𝔸 × α × α) ↦
      swap x.1 c ⬝ x.2.2.1 = swap x.2.1 c ⬝ x.2.2.2) := by
  apply equivariant_of_implies₂
  intro π c
  simp only [perm_name_eq, perm_eq_iff_eq_inv_perm]
  rintro ⟨a, b, x, y⟩
  dsimp only [Prod.perm_mk, perm_name_eq]
  rintro rfl
  rw [← mul_perm, ← mul_perm, ← mul_perm, ← mul_perm, mul_assoc, mul_assoc, swap_mul π,
    ← mul_assoc _ π, swap_inv, swap_inv, swap_mul π, inv_apply_self, inv_apply_self,
    inv_apply_self, mul_assoc]

theorem mk_eq_iff_exists [Nominal 𝔸 α] [Infinite 𝔸] {a b : 𝔸} {x y : α} :
    ⟨a⟩x = ⟨b⟩y ↔ ∃ c, c ≠ a ∧ c ≠ b ∧ c #[𝔸] x ∧ c #[𝔸] y ∧ swap a c ⬝ x = swap b c ⬝ y := by
  have := newNames_iff_exists _ (swap_perm_eq_swap_perm_equivariant (𝔸 := 𝔸) (α := α)) ⟨a, b, x, y⟩
  dsimp only at this
  rw [mk_eq_iff, this]
  simp only [Prod.fresh_iff, name_fresh_name_iff, ne_eq, and_assoc]

theorem mk_eq_iff_forall [Nominal 𝔸 α] [Infinite 𝔸] {a b : 𝔸} {x y : α} :
    ⟨a⟩x = ⟨b⟩y ↔ ∀ c, c ≠ a → c ≠ b → c #[𝔸] x → c #[𝔸] y → swap a c ⬝ x = swap b c ⬝ y := by
  have := newNames_iff_forall _ (swap_perm_eq_swap_perm_equivariant (𝔸 := 𝔸) (α := α)) ⟨a, b, x, y⟩
  dsimp only at this
  rw [mk_eq_iff, this]
  simp only [Prod.fresh_iff, name_fresh_name_iff, ne_eq, and_imp]

def lift₂ [HasPerm 𝔸 α] {𝔹 : Type*} [DecidableEq 𝔹] [MulPerm 𝔹 β] {γ : Sort*}
    (f : 𝔸 → α → 𝔹 → β → γ)
    (hf : ∀ (a b : 𝔸) (x y : α) (c d : 𝔹) (z w : β),
      (ν c, swap a c ⬝ x = swap b c ⬝ y) → (ν a, swap c a ⬝ z = swap d a ⬝ w) →
      f a x c z = f b y d w) :
    [𝔸]α → [𝔹]β → γ :=
  Quotient.lift₂
    (λ a b ↦ f a.name a.val b.name b.val)
    (λ _ _ _ _ ↦ hf _ _ _ _ _ _ _ _)

theorem lift_mk [HasPerm 𝔸 α] {β : Sort*} (f : 𝔸 → α → β)
    (hf : ∀ (a b : 𝔸) (x y : α), (ν c, swap a c ⬝ x = swap b c ⬝ y) → f a x = f b y)
    (a : 𝔸) (x : α) :
    lift f hf (⟨a⟩x) = f a x :=
  rfl

theorem perm_aux [MulPerm 𝔸 α] (π : Finperm 𝔸) (a b : 𝔸) (x y : α)
    (h : ν c, swap a c ⬝ x = swap b c ⬝ y) :
    ⟨π a⟩(π ⬝ x) = ⟨π b⟩(π ⬝ y) := by
  rw [mk_eq_iff]
  apply (h.perm π⁻¹).mono
  intro c h'
  rw [perm_eq_iff_eq_inv_perm, swap_inv] at h'
  rw [← mul_perm, swap_mul, inv_apply_self, ← mul_perm, swap_mul, inv_apply_self]
  rw [mul_perm, mul_perm, perm_left_cancel_iff]
  rw [h', ← mul_perm, swap_swap, one_perm]

instance [MulPerm 𝔸 α] : HasPerm 𝔸 [𝔸]α where
  perm π := lift (λ a x ↦ ⟨π a⟩(π ⬝ x)) (perm_aux π)

@[simp]
theorem perm_mk [MulPerm 𝔸 α] {π : Finperm 𝔸} {a : 𝔸} {x : α} :
    π ⬝ ⟨a⟩x = ⟨π a⟩(π ⬝ x) :=
  rfl

instance [MulPerm 𝔸 α] : MulPerm 𝔸 [𝔸]α where
  one_perm := by
    intro x
    induction x using ind; case mk a x =>
    simp only [perm_mk, coe_one, id_eq, one_perm]
  mul_perm := by
    intro π₁ π₂ x
    induction x using ind; case mk a x =>
    simp only [perm_mk, coe_mul, Function.comp_apply, mul_perm]

theorem supports_mk [MulPerm 𝔸 α] {a : 𝔸} {x : α} {s : Finset 𝔸}
    (h : Supports s x) :
    Supports (s \ {a}) (⟨a⟩x) := by
  intro π hπ
  rw [perm_mk, mk_eq_iff]
  apply (newNames_not_mem s).mono
  intro b hb
  rw [← inv_perm_eq_iff, ← mul_perm, ← mul_perm, swap_inv]
  apply h
  intro c hc
  simp only [Finset.mem_sdiff, Finset.mem_singleton, and_imp] at hπ
  simp only [perm_name_eq, coe_mul, Function.comp_apply]
  by_cases hc' : c = a
  · cases hc'
    simp only [coe_mul, Function.comp_apply, swap_apply_left, swap_apply_right]
  · have hcb : c ≠ b := by
      rintro rfl
      contradiction
    have hcπa : c ≠ π a := by
      rintro rfl
      have := hπ (π a) hc hc'
      rw [EmbeddingLike.apply_eq_iff_eq] at this
      contradiction
    rw [hπ c hc hc', swap_apply_of_ne_of_ne, swap_apply_of_ne_of_ne hcπa hcb]
    · rwa [swap_apply_of_ne_of_ne hcπa hcb]
    · rwa [swap_apply_of_ne_of_ne hcπa hcb]

instance [Nominal 𝔸 α] [Infinite 𝔸] : Nominal 𝔸 [𝔸]α where
  supported := by
    intro x
    induction x using ind; case mk a x =>
    exact ⟨supp 𝔸 x \ {a}, supports_mk (Nominal.supp_supports 𝔸 x)⟩

theorem mk_eq_iff' [Nominal 𝔸 α] [Infinite 𝔸] {a b : 𝔸} {x y : α} :
    ⟨a⟩x = ⟨b⟩y ↔ (a = b ∧ x = y) ∨ (a ≠ b ∧ a #[𝔸] y ∧ swap a b ⬝ x = y) := by
  constructor
  · intro h
    by_cases hab : a = b
    · cases hab
      simp only [mk_eq_iff, perm_left_cancel_iff, newNames_const] at h
      exact Or.inl ⟨rfl, h⟩
    refine Or.inr ⟨hab, ?_⟩
    rw [mk_eq_iff_exists] at h
    obtain ⟨c, hca, hcb, hcx, hcy, h⟩ := h
    have : a #[𝔸] y := by
      have := (hcx.perm (swap a c)).perm (swap b c)
      rwa [perm_name_eq, perm_name_eq, swap_apply_right, h, ← mul_perm, swap_swap,
        one_perm, swap_apply_of_ne_of_ne hab hca.symm] at this
    use this
    rw [← swap_perm_eq_of_fresh a c y this hcy, ← mul_perm, swap_pair a b c hab hcb.symm,
      mul_perm, perm_left_cancel_iff] at h
    rw [h, ← mul_perm, swap_swap, one_perm]
  · rintro (⟨rfl, rfl⟩ | ⟨hab, hay, rfl⟩)
    · rfl
    rw [mk_eq_iff_forall]
    intro c hca hcb hcx hcy
    rw [← mul_perm, swap_comm a b, ← swap_pair b a c hab.symm hca.symm,
      mul_perm, perm_left_cancel_iff, swap_perm_eq_of_fresh]
    · have := hay.perm (swap a b)
      simp only [perm_name_eq, swap_apply_left, ← mul_perm, swap_swap, one_perm] at this
      exact this
    · exact hcx

theorem supports_of_supports_abstract [MulPerm 𝔸 α] [Infinite 𝔸]
    {a : 𝔸} {x : α} {s : Finset 𝔸} (h : Supports s (⟨a⟩x)) :
    Supports (s ∪ {a}) x := by
  intro π hπ
  simp only [Finset.mem_union, Finset.mem_singleton] at hπ
  have := h π (λ a ha ↦ hπ a (.inl ha))
  simp only [perm_mk, mk_eq_iff] at this
  obtain ⟨c, hc⟩ := this.exists
  rwa [hπ a (.inr rfl), perm_left_cancel_iff] at hc

@[simp]
theorem supp_mk_eq [Nominal 𝔸 α] [Infinite 𝔸] (a : 𝔸) (x : α) :
    supp 𝔸 (⟨a⟩x) = supp 𝔸 x \ {a} := by
  apply subset_antisymm
  · rw [Nominal.supp_subset_iff]
    exact supports_mk (Nominal.supp_supports 𝔸 x)
  intro b hb
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hb
  rw [Nominal.mem_supp_iff] at hb ⊢
  intro s hs
  have := supports_of_supports_abstract hs
  have := hb.1 _ this
  simp only [Finset.mem_union, Finset.mem_singleton, hb.2, or_false] at this
  exact this

@[simp]
theorem mk_fresh_iff [Infinite 𝔸] [Nominal 𝔸 α] {a : 𝔸} {x : α} {b : 𝔸} :
    b #[𝔸] ⟨a⟩x ↔ b #[𝔸] x ∨ a = b := by
  rw [name_fresh_iff, name_fresh_iff, supp_mk_eq, Finset.mem_sdiff, Finset.mem_singleton]
  tauto

@[induction_eliminator]
theorem induction [Infinite 𝔸] [Nominal 𝔸 α] {motive : [𝔸]α → Prop}
    (mk : ν a, ∀ x, motive (⟨a⟩x)) :
    ∀ x, motive x := by
  intro x
  induction x using ind
  case mk a x =>
  obtain ⟨b, hbm, hbx, hba⟩ := (mk.and ((newNames_fresh x).and
    (newNames_not_mem {a}))).exists
  rw [Finset.mem_singleton] at hba
  suffices ⟨a⟩x = ⟨b⟩(swap a b ⬝ x) by
    rw [this]
    apply hbm
  rw [mk_eq_iff']
  refine Or.inr ⟨Ne.symm hba, ?_, rfl⟩
  have := hbx.perm (swap a b)
  rwa [perm_name_eq, swap_apply_right] at this

/-!
## Concretion
-/

/-- A class for types whose default element is a global section, like `Option α`.
This is used for concretion, to allow us to define the function in question everywhere. -/
class NominalDefault (𝔸 α : Type*) [DecidableEq 𝔸] [MulPerm 𝔸 α]
    extends Inhabited α where
  default_equivariant : Equivariant 𝔸 (default : α)

export NominalDefault (default_equivariant)

@[simp]
theorem perm_default [MulPerm 𝔸 α] [NominalDefault 𝔸 α] (π : Finperm 𝔸) :
    π ⬝ (default : α) = default :=
  default_equivariant π

open scoped Classical in
noncomputable def applyAux [Infinite 𝔸] [Nominal 𝔸 α] (default : α)
    (a : 𝔸) (x : α) (b : 𝔸) : α :=
  if b ∈ supp 𝔸 (⟨a⟩x) then
    default
  else
    swap a b ⬝ x

theorem applyAux_spec [Infinite 𝔸] [Nominal 𝔸 α] (default : α)
    (a b : 𝔸) (x y : α) (h : ν c, swap a c ⬝ x = swap b c ⬝ y) :
    applyAux default a x = applyAux default b y := by
  rw [← mk_eq_iff] at h
  ext c
  have := congr_arg (supp 𝔸) h
  simp only [supp_mk_eq, Finset.ext_iff, Finset.mem_sdiff, Finset.mem_singleton] at this
  unfold applyAux
  simp only [supp_mk_eq, Finset.mem_sdiff, Finset.mem_singleton, this]
  split_ifs with h'
  · rfl
  have h'' := h'
  rw [← this] at h''
  rw [mk_eq_iff_forall] at h
  obtain ⟨d, hdx, hdy, hd⟩ : ∃ _ : 𝔸, _ := ((newNames_fresh x).and
    ((newNames_fresh y).and (newNames_not_mem {a, b, c}))).exists
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  have hd' := h d hd.1 hd.2.1 hdx hdy
  simp only [not_and, Decidable.not_not] at h' h''
  by_cases hca : c = a
  · cases hca
    rw [swap_self, one_perm]
    by_cases hab : a = b
    · cases hab
      rw [swap_self, one_perm]
      have := h d hd.1 hd.1 hdx hdy
      rwa [perm_left_cancel_iff] at this
    · simp only [hab, imp_false] at h'
      rw [perm_eq_iff_eq_inv_perm, swap_inv] at hd'
      rw [hd', ← inv_perm_eq_iff, swap_inv, swap_comm b a, ← mul_perm, ← mul_perm,
        ← swap_triple' _ _ _ hab (Ne.symm hd.2.1), swap_perm_eq_of_fresh]
      · rwa [name_fresh_iff]
      · exact hdy
  · simp only [hca, imp_false] at h''
    by_cases hcb : c = b
    · cases hcb
      rw [← inv_perm_eq_iff, swap_inv] at hd'
      rw [swap_self, one_perm, perm_eq_iff_eq_inv_perm, swap_inv, ← hd', ← mul_perm,
        ← mul_perm, swap_comm a b, ← swap_triple' _ _ _ hca (Ne.symm hd.1), swap_perm_eq_of_fresh]
      · rwa [name_fresh_iff]
      · exact hdx
    · simp only [hcb, imp_false] at h'
      simp only [ne_eq, name_fresh_iff] at h
      exact h c hca hcb h'' h'

noncomputable def apply [Infinite 𝔸] [Nominal 𝔸 α] (default : α) :
    [𝔸]α → 𝔸 → α :=
  lift (applyAux default) (applyAux_spec default)

noncomputable def apply' [Infinite 𝔸] [Nominal 𝔸 α] [NominalDefault 𝔸 α] (x : [𝔸]α) :
    𝔸 →ₙ[𝔸] α where
  toFun := apply default x
  supported' := by
    rw [apply]
    induction x using ind; case mk b x =>
    use supp 𝔸 x ∪ {b}
    intro π hπ
    ext a
    simp only [Finset.mem_union, Finset.mem_singleton] at hπ
    simp only [lift_mk, FinpermMap.perm_def, perm_name_eq, FinpermMap.mk_apply, applyAux,
      supp_mk_eq, Finset.mem_sdiff, Finset.mem_singleton]
    split_ifs with h₁ h₂ h₂
    · rw [perm_default]
    · simp only [not_and, Decidable.not_not] at h₂
      have hb := congr_arg (π⁻¹ ·) (hπ b (.inr rfl))
      simp only [inv_apply_self] at hb
      rw [hb, EmbeddingLike.apply_eq_iff_eq] at h₁
      simp only [h₁.2, imp_false] at h₂
      have := hπ _ (.inl h₁.1)
      rw [apply_inv_self] at this
      rw [this] at h₂
      cases h₂ h₁.1
    · simp only [not_and, Decidable.not_not] at h₁
      have hb := congr_arg (π⁻¹ ·) (hπ b (.inr rfl))
      simp only [inv_apply_self] at hb
      rw [hb, EmbeddingLike.apply_eq_iff_eq] at h₁
      simp only [h₂.2, imp_false] at h₁
      have := hπ _ (.inl h₂.1)
      rw [← this, inv_apply_self] at h₁
      cases h₁ h₂.1
    · simp only [not_and, Decidable.not_not] at h₁ h₂
      rw [← mul_perm, mul_swap, apply_inv_self, hπ b (.inr rfl), mul_perm, perm_left_cancel_iff]
      exact Nominal.supp_supports 𝔸 x π (λ a ha ↦ hπ a (.inl ha))

/-!
## Functoriality
-/

def applyAux? [MulPerm 𝔸 α]
    (a : 𝔸) (x : α) (b : 𝔸) : Part α :=
  ⟨b #[𝔸] ⟨a⟩x, λ _ ↦ swap a b ⬝ x⟩

theorem applyAux?_spec [Infinite 𝔸] [Nominal 𝔸 α] (a b : 𝔸) (x y : α)
    (h : ν c, swap a c ⬝ x = swap b c ⬝ y) :
    applyAux? a x = applyAux? b y := by
  rw [← mk_eq_iff] at h
  ext c : 1
  rw [applyAux?, applyAux?]
  apply Part.ext'
  · have := congr_arg (c ∈ supp 𝔸 ·) h
    simp only [supp_mk_eq, Finset.mem_sdiff, Finset.mem_singleton, eq_iff_iff] at this
    simp only [name_fresh_iff, supp_mk_eq, Finset.mem_sdiff, Finset.mem_singleton,
      Decidable.not_not]
    exact not_congr this
  · intro h₁ h₂
    dsimp only at h₁ h₂ ⊢
    rw [mk_eq_iff'] at h
    obtain (⟨rfl, rfl⟩ | ⟨hab, hay, rfl⟩) := h
    · rfl
    simp only [name_fresh_iff, supp_mk_eq, Finset.mem_sdiff, Finset.mem_singleton, not_and,
      Decidable.not_not, Nominal.supp_perm_eq, Finset.mem_perm_iff, swap_inv, perm_name_eq,
      swap_apply_left] at h₁ h₂ hay
    by_cases hca : c = a
    · cases hca
      rw [swap_self, one_perm, swap_comm, ← mul_perm, swap_swap, one_perm]
    by_cases hcb : c = b
    · cases hcb
      rw [swap_self, one_perm]
    simp only [hca, imp_false] at h₁
    rw [perm_eq_iff_eq_inv_perm, swap_inv, ← mul_perm, ← mul_perm, swap_comm a c, swap_comm b c,
        ← swap_triple' c a b hca hab, swap_perm_eq_of_fresh]
    · rwa [name_fresh_iff]
    · rwa [name_fresh_iff]

noncomputable def apply? [Infinite 𝔸] [Nominal 𝔸 α] :
    [𝔸]α → 𝔸 → Part α :=
  lift applyAux? applyAux?_spec

theorem apply?_dom_iff [Infinite 𝔸] [Nominal 𝔸 α] (x : [𝔸]α) (a : 𝔸) :
    (apply? x a).Dom ↔ a #[𝔸] x := by
  induction x using ind
  case mk b x => rfl

theorem mk_apply?_eq [Infinite 𝔸] [Nominal 𝔸 α] {a : 𝔸} {x : α} {b : 𝔸} (hb : b #[𝔸] ⟨a⟩x) :
    apply? (⟨a⟩x) b = Part.some (swap a b ⬝ x) := by
  ext y
  rw [apply?, lift_mk, applyAux?]
  simp only [Part.mem_mk_iff, exists_prop, Part.mem_some_iff]
  tauto

noncomputable def elim? [Infinite 𝔸] [Nominal 𝔸 α] (f : 𝔸 → α → β) (x : [𝔸]α) :
    Part β :=
  fresh a, (x.apply? a).map (f a)

theorem elim?_spec' [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] (f : 𝔸 → α → β)
    (hf : ν a, ∀ x, a #[𝔸] f a x) (hf' : ν (a : 𝔸) (b : 𝔸), swap a b ⬝ f = f) (x : [𝔸]α) :
    ν a, x.elim? f = (x.apply? a).map (f a) := by
  sorry

theorem elim?_spec [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] (f : 𝔸 → α → β)
    (hf : ν a, ∀ x, a #[𝔸] f a x) (hf' : ν (a : 𝔸) (b : 𝔸), swap a b ⬝ f = f) (x : [𝔸]α) :
    ν a, x.elim? f = (x.apply? a).map (f a) := by
  apply fresh_spec
  · apply hf.mono
    intro a h
    induction x using ind
    case mk b x =>
    rw [apply?, lift_mk, applyAux?, Part.map]
    dsimp only
    by_cases ha : a #[𝔸] ⟨b⟩x
    · rw [Part.fresh_iff_of_dom ha]
      simp only [Function.comp_apply]
      apply h
    · exact Part.fresh_of_not_dom ha a
  · simp only [finitelySupported_iff, funext_iff, Function.perm_def, swap_inv, perm_name_eq,
      Part.ext_iff, Part.mem_perm_iff, Part.mem_map_iff]
    induction x using ind
    case mk a x =>
    -- apply hf.mono
    -- intro a x
    apply (hf'.and ((newNames_fresh x).and (newNames_not_mem {a}))).mono
    rintro b ⟨hb₁, hb₂, hb₃⟩
    apply (hb₁.and ((newNames_fresh x).and (newNames_not_mem {a, b}))).mono
    rintro c ⟨hc₁, hc₂, hc₃⟩ d y
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hb₃ hc₃
    by_cases hdb : d = b
    · cases hdb
      simp only [swap_apply_left, mk_apply?_eq (mk_fresh_iff.mpr (Or.inl hc₂)), Part.mem_some_iff,
        exists_eq_left, mk_apply?_eq (mk_fresh_iff.mpr (Or.inl hb₂))]
    -- apply (newNames_not_mem {a, b}).mono
    -- have := newNames_fresh x
    sorry

end Abstract
