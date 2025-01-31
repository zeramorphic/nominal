import Nominal.Instances
import Nominal.Quantifier

open Finperm MulAction

variable {𝔸 α β : Type*} [DecidableEq 𝔸]

structure WithName (𝔸 : Type*) (α : Type*) where
  name : 𝔸
  val : α

namespace WithName

protected def rel [SMul (Finperm 𝔸) α] (x y : WithName 𝔸 α) : Prop :=
  ν a, swap x.name a • x.val = swap y.name a • y.val

theorem rel_isEqv [SMul (Finperm 𝔸) α] :
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

protected instance setoid [SMul (Finperm 𝔸) α] : Setoid (WithName 𝔸 α) where
  r := WithName.rel
  iseqv := rel_isEqv

end WithName

def Abstract (𝔸 : Type*) [DecidableEq 𝔸] (α : Type*) [SMul (Finperm 𝔸) α] :=
  Quotient (WithName.setoid : Setoid (WithName 𝔸 α))

namespace Abstract

notation:max "["𝔸"]" α:max => Abstract 𝔸 α

def mk [SMul (Finperm 𝔸) α] (a : 𝔸) (x : α) : [𝔸]α :=
  Quotient.mk WithName.setoid ⟨a, x⟩

notation "⟨"a"⟩" x:max => Abstract.mk a x

theorem sound [SMul (Finperm 𝔸) α] {a b : 𝔸} {x y : α} (h : ν c, swap a c • x = swap b c • y) :
    ⟨a⟩x = ⟨b⟩y :=
  Quotient.sound h

def lift [SMul (Finperm 𝔸) α] {β : Sort*} (f : 𝔸 → α → β)
    (hf : ∀ (a b : 𝔸) (x y : α), (ν c, swap a c • x = swap b c • y) → f a x = f b y) :
    [𝔸]α → β :=
  Quotient.lift (λ x ↦ f x.name x.val) (λ x y ↦ hf x.name y.name x.val y.val)

@[induction_eliminator]
theorem ind [SMul (Finperm 𝔸) α] {motive : [𝔸]α → Prop} (mk : ∀ a x, motive (⟨a⟩x)) :
    ∀ x, motive x :=
  Quotient.ind (λ x ↦ mk x.name x.val)

theorem exact [SMul (Finperm 𝔸) α] {a b : 𝔸} {x y : α} (h : ⟨a⟩x = ⟨b⟩y) :
    ν c, swap a c • x = swap b c • y :=
  Quotient.exact h

theorem mk_eq_iff [SMul (Finperm 𝔸) α] {a b : 𝔸} {x y : α} :
    ⟨a⟩x = ⟨b⟩y ↔ ν c, swap a c • x = swap b c • y :=
  ⟨exact, sound⟩

theorem swap_smul_eq_swap_smul_equivariant [MulAction (Finperm 𝔸) α] :
    EquivariantRel 𝔸 (λ c (x : 𝔸 × 𝔸 × α × α) ↦
      swap x.1 c • x.2.2.1 = swap x.2.1 c • x.2.2.2) := by
  apply equivariantRel_of_implies
  intro π c
  simp only [smul_name_eq, smul_eq_iff_eq_inv_smul, smul_inv]
  rintro ⟨a, b, x, y⟩
  dsimp only [Prod.smul_mk, smul_name_eq]
  rintro rfl
  rw [smul_smul, smul_smul, smul_smul, smul_smul, mul_assoc, mul_assoc, swap_mul π,
    ← mul_assoc _ π, swap_inv, swap_inv, swap_mul π, inv_apply_self, inv_apply_self,
    inv_apply_self, mul_assoc]

theorem mk_eq_iff_exists [Nominal 𝔸 α] [Infinite 𝔸] {a b : 𝔸} {x y : α} :
    ⟨a⟩x = ⟨b⟩y ↔ ∃ c, c ≠ a ∧ c ≠ b ∧ c #[𝔸] x ∧ c #[𝔸] y ∧ swap a c • x = swap b c • y := by
  have := newNames_iff_exists _ (swap_smul_eq_swap_smul_equivariant (𝔸 := 𝔸) (α := α)) ⟨a, b, x, y⟩
  dsimp only at this
  rw [mk_eq_iff, this]
  simp only [Prod.fresh_iff, name_fresh_name_iff, ne_eq, and_assoc]

theorem mk_eq_iff_forall [Nominal 𝔸 α] [Infinite 𝔸] {a b : 𝔸} {x y : α} :
    ⟨a⟩x = ⟨b⟩y ↔ ∀ c, c ≠ a → c ≠ b → c #[𝔸] x → c #[𝔸] y → swap a c • x = swap b c • y := by
  have := newNames_iff_forall _ (swap_smul_eq_swap_smul_equivariant (𝔸 := 𝔸) (α := α)) ⟨a, b, x, y⟩
  dsimp only at this
  rw [mk_eq_iff, this]
  simp only [Prod.fresh_iff, name_fresh_name_iff, ne_eq, and_imp]

def lift₂ [SMul (Finperm 𝔸) α] {𝔹 : Type*} [DecidableEq 𝔹] [SMul (Finperm 𝔹) β] {γ : Sort*}
    (f : 𝔸 → α → 𝔹 → β → γ)
    (hf : ∀ (a b : 𝔸) (x y : α) (c d : 𝔹) (z w : β),
      (ν c, swap a c • x = swap b c • y) → (ν a, swap c a • z = swap d a • w) →
      f a x c z = f b y d w) :
    [𝔸]α → [𝔹]β → γ :=
  Quotient.lift₂
    (λ a b ↦ f a.name a.val b.name b.val)
    (λ _ _ _ _ ↦ hf _ _ _ _ _ _ _ _)

theorem lift_mk [SMul (Finperm 𝔸) α] {β : Sort*} (f : 𝔸 → α → β)
    (hf : ∀ (a b : 𝔸) (x y : α), (ν c, swap a c • x = swap b c • y) → f a x = f b y)
    (a : 𝔸) (x : α) :
    lift f hf (⟨a⟩x) = f a x :=
  rfl

theorem smul_aux [MulAction (Finperm 𝔸) α] (π : Finperm 𝔸) (a b : 𝔸) (x y : α)
    (h : ν c, swap a c • x = swap b c • y) :
    ⟨π a⟩(π • x) = ⟨π b⟩(π • y) := by
  rw [mk_eq_iff]
  apply (h.smul π⁻¹).mono
  intro c h'
  rw [smul_eq_iff_eq_inv_smul, swap_inv] at h'
  rw [smul_smul, swap_mul, inv_apply_self, smul_smul, swap_mul, inv_apply_self]
  rw [mul_smul, mul_smul, smul_left_cancel_iff]
  rw [h', smul_smul, swap_swap, one_smul]

instance [MulAction (Finperm 𝔸) α] : SMul (Finperm 𝔸) [𝔸]α where
  smul π := lift (λ a x ↦ ⟨π a⟩(π • x)) (smul_aux π)

@[simp]
theorem smul_mk [MulAction (Finperm 𝔸) α] {π : Finperm 𝔸} {a : 𝔸} {x : α} :
    π • ⟨a⟩x = ⟨π a⟩(π • x) :=
  rfl

instance [MulAction (Finperm 𝔸) α] : MulAction (Finperm 𝔸) [𝔸]α where
  one_smul := by
    intro x
    induction x; case mk a x =>
    simp only [smul_mk, coe_one, id_eq, one_smul]
  mul_smul := by
    intro π₁ π₂ x
    induction x; case mk a x =>
    simp only [smul_mk, coe_mul, Function.comp_apply, mul_smul]

theorem supports_mk [MulAction (Finperm 𝔸) α] {a : 𝔸} {x : α} {s : Finset 𝔸}
    (h : Supports (Finperm 𝔸) (s : Set 𝔸) x) :
    Supports (Finperm 𝔸) ((s \ {a} : Finset 𝔸) : Set 𝔸) (⟨a⟩x) := by
  intro π hπ
  rw [smul_mk, mk_eq_iff]
  apply (newNames_not_mem s).mono
  intro b hb
  rw [← inv_smul_eq_iff, smul_smul, smul_smul, swap_inv]
  apply h
  intro c hc
  simp only [Finset.coe_sdiff, Finset.coe_singleton, Set.mem_diff, Finset.mem_coe,
    Set.mem_singleton_iff, smul_name_eq, and_imp] at hπ
  simp only [smul_name_eq, coe_mul, Function.comp_apply]
  by_cases hc' : c = a
  · cases hc'
    simp only [coe_mul, Function.comp_apply, swap_apply_left, swap_apply_right]
  · have hcb : c ≠ b := by
      rintro rfl
      contradiction
    have hcπa : c ≠ π a := by
      rintro rfl
      have := hπ hc hc'
      rw [EmbeddingLike.apply_eq_iff_eq] at this
      contradiction
    rw [hπ hc hc', swap_apply_of_ne_of_ne, swap_apply_of_ne_of_ne hcπa hcb]
    · rwa [swap_apply_of_ne_of_ne hcπa hcb]
    · rwa [swap_apply_of_ne_of_ne hcπa hcb]

instance [Nominal 𝔸 α] [Infinite 𝔸] : Nominal 𝔸 [𝔸]α where
  supported := by
    intro x
    induction x; case mk a x =>
    exact ⟨supp 𝔸 x \ {a}, supports_mk (Nominal.supp_supports 𝔸 x)⟩

theorem mk_eq_iff' [Nominal 𝔸 α] [Infinite 𝔸] {a b : 𝔸} {x y : α} :
    ⟨a⟩x = ⟨b⟩y ↔ (a = b ∧ x = y) ∨ (a ≠ b ∧ a #[𝔸] y ∧ swap a b • x = y) := by
  constructor
  · intro h
    by_cases hab : a = b
    · cases hab
      simp only [mk_eq_iff, smul_left_cancel_iff, newNames_const] at h
      exact Or.inl ⟨rfl, h⟩
    refine Or.inr ⟨hab, ?_⟩
    rw [mk_eq_iff_exists] at h
    obtain ⟨c, hca, hcb, hcx, hcy, h⟩ := h
    have : a #[𝔸] y := by
      have := (hcx.smul (swap a c)).smul (swap b c)
      rwa [smul_name_eq, smul_name_eq, swap_apply_right, h, smul_smul, swap_swap,
        one_smul, swap_apply_of_ne_of_ne hab hca.symm] at this
    use this
    rw [← swap_smul_eq_of_fresh a c y this hcy, smul_smul, swap_pair a b c hab hcb.symm,
      mul_smul, smul_left_cancel_iff] at h
    rw [h, smul_smul, swap_swap, one_smul]
  · rintro (⟨rfl, rfl⟩ | ⟨hab, hay, rfl⟩)
    · rfl
    rw [mk_eq_iff_forall]
    intro c hca hcb hcx hcy
    rw [smul_smul, swap_comm a b, ← swap_pair b a c hab.symm hca.symm,
      mul_smul, smul_left_cancel_iff, swap_smul_eq_of_fresh]
    · have := hay.smul (swap a b)
      simp only [smul_name_eq, swap_apply_left, smul_smul, swap_swap, one_smul] at this
      exact this
    · exact hcx

theorem supports_of_supports_abstract [MulAction (Finperm 𝔸) α] [Infinite 𝔸]
    {a : 𝔸} {x : α} {s : Finset 𝔸} (h : Supports (Finperm 𝔸) (s : Set 𝔸) (⟨a⟩x)) :
    Supports (Finperm 𝔸) ((s ∪ {a} : Finset 𝔸) : Set 𝔸) x := by
  intro π hπ
  simp only [Finset.coe_union, Finset.coe_singleton, Set.union_singleton, Set.mem_insert_iff,
    Finset.mem_coe, smul_name_eq, forall_eq_or_imp] at hπ
  have := h π hπ.2
  simp only [smul_mk, mk_eq_iff] at this
  obtain ⟨c, hc⟩ := this.exists
  rwa [hπ.1, smul_left_cancel_iff] at hc

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

/-!
## Concretion
-/

/-- A class for types whose default element is a global section, like `Option α`.
This is used for concretion, to allow us to define the function in question everywhere. -/
class NominalDefault (𝔸 α : Type*) [DecidableEq 𝔸] [MulAction (Finperm 𝔸) α]
    extends Inhabited α where
  default_isGlobalSection : IsGlobalSection 𝔸 (default : α)

export NominalDefault (default_isGlobalSection)

@[simp]
theorem smul_default [MulAction (Finperm 𝔸) α] [NominalDefault 𝔸 α] (π : Finperm 𝔸) :
    π • (default : α) = default :=
  default_isGlobalSection π

open scoped Classical in
noncomputable def mapAux [Infinite 𝔸] [Nominal 𝔸 α] [NominalDefault 𝔸 α]
    (a : 𝔸) (x : α) (b : 𝔸) : α :=
  if b ∈ supp 𝔸 (⟨a⟩x) then
    default
  else
    swap a b • x

theorem mapAux_spec [Infinite 𝔸] [Nominal 𝔸 α] [NominalDefault 𝔸 α]
    (a b : 𝔸) (x y : α) (h : ν c, swap a c • x = swap b c • y) :
    mapAux a x = mapAux b y := by
  rw [← mk_eq_iff] at h
  ext c
  have := congr_arg (supp 𝔸) h
  simp only [supp_mk_eq, Finset.ext_iff, Finset.mem_sdiff, Finset.mem_singleton] at this
  unfold mapAux
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
    rw [swap_self, one_smul]
    by_cases hab : a = b
    · cases hab
      rw [swap_self, one_smul]
      have := h d hd.1 hd.1 hdx hdy
      rwa [smul_left_cancel_iff] at this
    · simp only [hab, imp_false] at h'
      rw [smul_eq_iff_eq_inv_smul, swap_inv] at hd'
      rw [hd', ← inv_smul_eq_iff, swap_inv, swap_comm b a, smul_smul, smul_smul,
        ← swap_triple' _ _ _ hab (Ne.symm hd.2.1), swap_smul_eq_of_fresh]
      · rwa [name_fresh_iff]
      · exact hdy
  · simp only [hca, imp_false] at h''
    by_cases hcb : c = b
    · cases hcb
      rw [← inv_smul_eq_iff, swap_inv] at hd'
      rw [swap_self, one_smul, smul_eq_iff_eq_inv_smul, swap_inv, ← hd', smul_smul,
        smul_smul, swap_comm a b, ← swap_triple' _ _ _ hca (Ne.symm hd.1), swap_smul_eq_of_fresh]
      · rwa [name_fresh_iff]
      · exact hdx
    · simp only [hcb, imp_false] at h'
      simp only [ne_eq, name_fresh_iff] at h
      exact h c hca hcb h'' h'

noncomputable def map [Infinite 𝔸] [Nominal 𝔸 α] [NominalDefault 𝔸 α] (x : [𝔸]α) :
    𝔸 →ₙ[𝔸] α where
  toFun := lift mapAux mapAux_spec x
  supported' := by
    induction x; case mk b x =>
    use supp 𝔸 x ∪ {b}
    intro π hπ
    ext a
    simp only [Finset.coe_union, Finset.coe_singleton, Set.union_singleton, Set.mem_insert_iff,
      Finset.mem_coe, smul_name_eq, forall_eq_or_imp] at hπ
    simp only [lift_mk, FinpermMap.smul_def, smul_name_eq, FinpermMap.mk_apply, mapAux, supp_mk_eq,
      Finset.mem_sdiff, Finset.mem_singleton, smul_ite, smul_default]
    split_ifs with h₁ h₂ h₂
    · rfl
    · simp only [not_and, Decidable.not_not] at h₂
      have hb := congr_arg (π⁻¹ ·) hπ.1
      simp only [inv_apply_self] at hb
      rw [hb, EmbeddingLike.apply_eq_iff_eq] at h₁
      simp only [h₁.2, imp_false] at h₂
      have := hπ.2 (π⁻¹ a) h₁.1
      rw [apply_inv_self] at this
      rw [this] at h₂
      cases h₂ h₁.1
    · simp only [not_and, Decidable.not_not] at h₁
      have hb := congr_arg (π⁻¹ ·) hπ.1
      simp only [inv_apply_self] at hb
      rw [hb, EmbeddingLike.apply_eq_iff_eq] at h₁
      simp only [h₂.2, imp_false] at h₁
      have := hπ.2 a h₂.1
      rw [← this, inv_apply_self] at h₁
      cases h₁ h₂.1
    · simp only [not_and, Decidable.not_not] at h₁ h₂
      rw [smul_smul, mul_swap, apply_inv_self, hπ.1, mul_smul, smul_left_cancel_iff]
      exact Nominal.supp_supports 𝔸 x π hπ.2

end Abstract
