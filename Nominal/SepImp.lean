import Nominal.SepProd

open Finperm Rel

/-!
# Separating implication

We define *separating implication*, the right adjoint to the functor `- ∗[𝔸] α`.
-/

/-- The *separating implication* of `α` and `β` with respect to the name set `𝔸`.
We use the definition from section 3.4 of Nominal Sets (Pitts). -/
@[ext]
structure SepImp (𝔸 : Type*) [DecidableEq 𝔸] (α β : Type*) [MulPerm 𝔸 α] [MulPerm 𝔸 β] where
  rel : α → β → Prop
  rel_fs : FinitelySupported 𝔸 rel
  rel_coinjective : Coinjective rel
  mem_dom_iff x : x ∈ dom rel ↔ x #[𝔸] rel
  mem_supp_iff a : a ∈ supp 𝔸 rel ↔ ∃ x y, rel x y ∧ a ∈ supp 𝔸 y \ supp 𝔸 x

@[inherit_doc] notation:25 α " -∗["𝔸"] " β:0 => SepImp 𝔸 α β

theorem Rel.Coinjective.perm {𝔸 : Type*} [DecidableEq 𝔸] {α β : Type*}
    [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    {r : α → β → Prop} (h : Coinjective r) (π : Finperm 𝔸) :
    Coinjective (π ⬝ r) := by
  constructor
  intro y₁ y₂ x h₁ h₂
  rw [Function.perm_def, Function.perm_def, IsDiscrete.perm_eq] at h₁ h₂
  have := h.coinjective h₁ h₂
  rwa [perm_left_cancel_iff] at this

@[simp]
theorem Rel.dom_perm {𝔸 : Type*} [DecidableEq 𝔸] {α β : Type*}
    [MulPerm 𝔸 α] [MulPerm 𝔸 β] (r : α → β → Prop) (π : Finperm 𝔸) :
    dom (π ⬝ r) = (π⁻¹ ⬝ ·) ⁻¹' dom r := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    use π⁻¹ ⬝ y
    exact hy
  · rintro ⟨y, hy⟩
    use π ⬝ y
    rw [Function.perm_def, Function.perm_def, inv_perm_perm]
    exact hy

namespace SepImp

variable {𝔸 : Type*} [DecidableEq 𝔸] {α β γ : Type*}

theorem mem_dom_iff_perm [MulPerm 𝔸 α] [MulPerm 𝔸 β] {f : α -∗[𝔸] β} {π : Finperm 𝔸} (x : α) :
    x ∈ dom (π ⬝ f.rel) ↔ x #[𝔸] (π ⬝ f.rel) := by
  rw [dom_perm, Set.mem_preimage, fresh_perm_iff_inv_perm_fresh, f.mem_dom_iff]

theorem mem_supp_iff_perm [MulPerm 𝔸 α] [MulPerm 𝔸 β] {f : α -∗[𝔸] β} {π : Finperm 𝔸} (a : 𝔸) :
    a ∈ supp 𝔸 (π ⬝ f.rel) ↔ ∃ x y, f.rel (π⁻¹ ⬝ x) (π⁻¹ ⬝ y) ∧ a ∈ supp 𝔸 y \ supp 𝔸 x := by
  rw [supp_perm_eq, Finset.mem_perm, f.mem_supp_iff]
  constructor
  · rintro ⟨x, y, h₁, h₂⟩
    refine ⟨π ⬝ x, π ⬝ y, ?_, ?_⟩
    · rwa [inv_perm_perm, inv_perm_perm]
    · simp only [supp_perm_eq, Finset.mem_sdiff, Finset.mem_perm] at h₂ ⊢
      exact h₂
  · rintro ⟨x, y, h₁, h₂⟩
    refine ⟨π⁻¹ ⬝ x, π⁻¹ ⬝ y, h₁, ?_⟩
    simp only [Finset.mem_sdiff] at h₂
    simp only [supp_perm_eq, perm_name_eq, Finset.mem_sdiff, Finset.mem_perm,
      _root_.inv_inv, apply_inv_self]
    exact h₂

instance [MulPerm 𝔸 α] [MulPerm 𝔸 β] : HasPerm 𝔸 (α -∗[𝔸] β) where
  perm π f := ⟨π ⬝ f.rel, f.rel_fs.perm π,
    f.rel_coinjective.perm π, mem_dom_iff_perm, mem_supp_iff_perm⟩

@[simp]
theorem perm_rel [MulPerm 𝔸 α] [MulPerm 𝔸 β] (f : α -∗[𝔸] β) (π : Finperm 𝔸) :
    (π ⬝ f).rel = π ⬝ f.rel :=
  rfl

instance [MulPerm 𝔸 α] [MulPerm 𝔸 β] : MulPerm 𝔸 (α -∗[𝔸] β) where
  one_perm f := by
    ext : 1
    simp only [perm_rel, one_perm]
  mul_perm π₁ π₂ f := by
    ext : 1
    simp only [perm_rel, mul_perm]

@[simp]
theorem supports_iff [MulPerm 𝔸 α] [MulPerm 𝔸 β] {f : α -∗[𝔸] β} {s : Finset 𝔸} :
    Supports s f ↔ Supports s f.rel := by
  simp only [Supports, SepImp.ext_iff, perm_rel]

instance [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] : Nominal 𝔸 (α -∗[𝔸] β) where
  supported f := by
    use supp 𝔸 f.rel
    intro π hπ
    ext : 1
    exact supp_supports' f.rel f.rel_fs π hπ

@[simp]
theorem supp_eq [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] (f : α -∗[𝔸] β) :
    supp 𝔸 f = supp 𝔸 f.rel := by
  ext a
  simp only [Nominal.mem_supp_iff, supports_iff, mem_supp_iff' f.rel f.rel_fs]

@[simp]
theorem fresh_iff [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] (f : α -∗[𝔸] β) [MulPerm 𝔸 γ] (x : γ) :
    x #[𝔸] f ↔ x #[𝔸] f.rel := by
  rw [fresh_def, fresh_def, supp_eq]

/-!
# Unit and counit
-/

theorem supports_unit [Infinite 𝔸] [MulPerm 𝔸 α] [Nominal 𝔸 β] (x : β) :
    Supports (supp 𝔸 x) (λ y (z : β ∗[𝔸] α) ↦ z.fst = x ∧ z.snd = y) := by
  intro π hπ
  ext y z
  have := Nominal.supp_supports 𝔸 x π hπ
  simp only [Function.perm_def, SepProd.perm_fst, SepProd.perm_snd, perm_left_cancel_iff,
    IsDiscrete.perm_eq]
  constructor
  · rintro ⟨rfl, rfl⟩
    rw [perm_inv_perm] at this
    rw [← this]
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rw [perm_eq_iff_eq_inv_perm] at this
    rw [← this]
    exact ⟨rfl, rfl⟩

theorem unit_supp [Infinite 𝔸] [MulPerm 𝔸 α] [Nominal 𝔸 β] (x : β) :
    IsEmpty α ∨ supp 𝔸 (λ (y : α) (z : β ∗[𝔸] α) ↦ z.fst = x ∧ z.snd = y) = supp 𝔸 x := by
  rw [or_iff_not_imp_left, not_isEmpty_iff]
  intro
  apply subset_antisymm
  · exact supp_minimal _ _ (supports_unit x)
  intro a ha
  rw [Nominal.mem_supp_iff_names_infinite] at ha
  rw [mem_supp_iff' _ ⟨_, supports_unit x⟩]
  intro s hs
  by_contra ha'
  obtain ⟨y, hy⟩ := exists_fresh 𝔸 α x
  obtain ⟨b, hb₁, hb₂⟩ := ha.exists_not_mem_finset s
  have := hs (swap a b) ?_
  · simp only [funext_iff, Function.perm_def, swap_inv, SepProd.perm_fst, SepProd.perm_snd,
      perm_left_cancel_iff, IsDiscrete.perm_eq, eq_iff_iff, and_congr_left_iff] at this
    have := this y ⟨x, y, hy.comm⟩ rfl
    simp only [iff_true] at this
    contradiction
  · intro c hc
    rw [swap_apply_of_ne_of_ne]
    · rintro rfl
      contradiction
    · rintro rfl
      contradiction

theorem unit_mem_dom_iff [Infinite 𝔸] [MulPerm 𝔸 α] [Nominal 𝔸 β] (x : β) (y : α) :
    (y ∈ dom λ (z : α) (w : β ∗[𝔸] α) ↦ w.fst = x ∧ w.snd = z) ↔
    y #[𝔸] λ (z : α) (w : β ∗[𝔸] α) ↦ w.fst = x ∧ w.snd = z := by
  obtain (hα | hsupp) := unit_supp x (𝔸 := 𝔸) (α := α)
  · cases hα.false y
  rw [fresh_def, hsupp, ← fresh_def, dom]
  constructor
  · rintro ⟨z, rfl, rfl⟩
    exact z.sep.comm
  · intro h
    exact ⟨⟨x, y, h.comm⟩, rfl, rfl⟩

theorem unit_mem_supp_iff [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] (x : β) (a : 𝔸) :
    (a ∈ supp 𝔸 λ (z : α) (w : β ∗[𝔸] α) ↦ w.fst = x ∧ w.snd = z) ↔
    ∃ (y : α) (z : β ∗[𝔸] α), (z.fst = x ∧ z.snd = y) ∧ a ∈ supp 𝔸 z \ supp 𝔸 y := by
  obtain hα | hα := isEmpty_or_nonempty α
  · simp only [IsDiscrete.supp_eq, Finset.not_mem_empty, SepProd.supp_eq, Finset.union_empty,
      Finset.sdiff_empty, IsEmpty.exists_iff]
  · have hsupp := Or.resolve_left (unit_supp x (𝔸 := 𝔸) (α := α)) (not_isEmpty_of_nonempty α)
    rw [hsupp]
    constructor
    · intro ha
      obtain ⟨y, hy⟩ := exists_fresh 𝔸 α x
      refine ⟨y, ⟨x, y, hy.comm⟩, ⟨rfl, rfl⟩, ?_⟩
      rw [SepProd.supp_eq, Finset.mem_sdiff, Finset.mem_union]
      refine ⟨Or.inl ha, ?_⟩
      rintro ha'
      rw [fresh_def, Finset.disjoint_iff_ne] at hy
      exact hy a ha' a ha rfl
    · rintro ⟨y, z, ⟨rfl, rfl⟩, h⟩
      rw [SepProd.supp_eq, Finset.mem_sdiff, Finset.mem_union] at h
      tauto

/-- The unit of the adjunction between separated product and separating implication. -/
def unit [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] (x : β) : α -∗[𝔸] β ∗[𝔸] α where
  rel y z := z.fst = x ∧ z.snd = y
  rel_fs := ⟨supp 𝔸 x, supports_unit x⟩
  rel_coinjective := by constructor; aesop
  mem_dom_iff := unit_mem_dom_iff x
  mem_supp_iff := unit_mem_supp_iff x

/-- Apply a separating implication to an object.
The result of this computation is meaningful only when `x #[𝔸] f`. -/
noncomputable def apply [MulPerm 𝔸 α] [MulPerm 𝔸 β] (f : α -∗[𝔸] β) (x : α) [Nonempty β] : β :=
  Classical.epsilon (λ y ↦ f.rel x y)

theorem apply_spec [MulPerm 𝔸 α] [MulPerm 𝔸 β] (f : α -∗[𝔸] β) (x : α) [Nonempty β]
    (h : x #[𝔸] f.rel) :
    f.rel x (f.apply x) :=
  Classical.epsilon_spec ((f.mem_dom_iff x).mpr h)

theorem nonempty_of_sepProd [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    (x : (α -∗[𝔸] β) ∗[𝔸] α) : Nonempty β :=
  ⟨((x.fst.mem_dom_iff x.snd).mpr ((x.fst.fresh_iff x.snd).mp x.sep.comm)).choose⟩

/-- The counit of the adjunction between separated product and separating implication. -/
noncomputable def ev [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : (α -∗[𝔸] β) ∗[𝔸] α) : β :=
  haveI : Nonempty β := nonempty_of_sepProd x
  x.fst.apply x.snd

theorem ev_spec [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : (α -∗[𝔸] β) ∗[𝔸] α) :
    x.fst.rel x.snd (ev x) :=
  haveI : Nonempty β := nonempty_of_sepProd x
  apply_spec _ _ ((x.fst.fresh_iff x.snd).mp x.sep.comm)

/-!
# Transpose

This follows the proof of "Generalised Name Abstraction for Nominal Sets", Clouston.
-/

def transpAux [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (y : β) (x : α) (z : γ) : Prop :=
  (∀ x' : α, ∀ h, ∀ a ∈ supp 𝔸 x, a ∈ supp 𝔸 x' ∨ a ∉ supp 𝔸 (f ⟨y, x', h⟩)) ∧
  ∃ s : Finset 𝔸, ∃ hs : Disjoint (supp 𝔸 y ∪ supp 𝔸 x) s,
    ∃ e : (supp 𝔸 y ∩ supp 𝔸 x : Finset 𝔸) ≃ s,
    ∃ h, z = f ⟨swaps (hs.mono_left Finset.inter_subset_union) e ⬝ y, x, h⟩

theorem exists_disjoint [Infinite 𝔸] (s : Finset 𝔸) (t : Finset 𝔸) :
    ∃ u : Finset 𝔸, Disjoint t u ∧ Nonempty (s ≃ u) := by
  obtain ⟨u, hu₁, hu₂⟩ := Infinite.exists_superset_card_eq t
    (s.card + t.card) (t.card.le_add_left s.card)
  refine ⟨u \ t, Finset.disjoint_sdiff, ⟨?_⟩⟩
  apply Finset.equivOfCardEq
  have := Finset.card_sdiff_add_card_eq_card hu₁
  rw [hu₂, add_left_inj] at this
  exact this.symm

def _root_.Equiv.perm {α : Type*} [MulPerm 𝔸 α] {s t : Finset α}
    (e : s ≃ t) (π : Finperm 𝔸) :
    (π ⬝ s : Finset α) ≃ (π ⬝ t : Finset α) where
  toFun x := ⟨π ⬝ (e ⟨π⁻¹ ⬝ x, (Finset.mem_perm π x.val s).mp x.prop⟩), by
    rw [Finset.mem_perm, inv_perm_perm]
    exact (e ⟨π⁻¹ ⬝ x, _⟩).prop⟩
  invFun x := ⟨π ⬝ (e.symm ⟨π⁻¹ ⬝ x, (Finset.mem_perm π x.val t).mp x.prop⟩), by
    rw [Finset.mem_perm, inv_perm_perm]
    exact (e.symm ⟨π⁻¹ ⬝ x, _⟩).prop⟩
  left_inv x := by
    simp only [inv_perm_perm, Subtype.coe_eta, Equiv.symm_apply_apply, perm_inv_perm]
  right_inv x := by
    simp only [inv_perm_perm, Subtype.coe_eta, Equiv.apply_symm_apply, perm_inv_perm]

theorem transpAux_dom_eq [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (y : β) (x : α) :
    x ∈ dom (transpAux f y) ↔
    ∀ x' : α, ∀ h, ∀ a ∈ supp 𝔸 x, a ∈ supp 𝔸 x' ∨ a ∉ supp 𝔸 (f ⟨y, x', h⟩) := by
  simp only [dom, transpAux, Set.mem_setOf_eq, exists_and_left, and_iff_left_iff_imp]
  intro h
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_disjoint (supp 𝔸 y ∩ supp 𝔸 x) (supp 𝔸 y ∪ supp 𝔸 x)
  refine ⟨_, s, hs, e, ?_, rfl⟩
  rw [Finset.disjoint_union_left, Finset.disjoint_iff_ne, Finset.disjoint_iff_ne] at hs
  rw [fresh_def, Finset.disjoint_iff_ne]
  rintro a hay _ hax rfl
  rw [supp_perm_eq, Finset.mem_perm, perm_name_eq, swaps_inv] at hay
  by_cases ha : a ∈ supp 𝔸 y
  · rw [swaps_eq_of_mem₁ a (Finset.mem_inter_of_mem ha hax)] at hay
    have := (e ⟨a, Finset.mem_inter_of_mem ha hax⟩).prop
    exact hs.1 _ hay _ this rfl
  · rw [swaps_eq_of_not_mem] at hay
    · contradiction
    · simp only [Finset.mem_inter, ha, false_and, not_false_eq_true]
    · intro ha'
      exact hs.2 a hax a ha' rfl

theorem transpAux_equivariant' [Infinite 𝔸] [MulPerm 𝔸 α] [Nominal 𝔸 β] [MulPerm 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) (x : α) (z : γ) (π : Finperm 𝔸) :
    transpAux f y x z → transpAux f (π ⬝ y) (π ⬝ x) (π ⬝ z) := by
  rintro ⟨h, s, hs, e, hx, rfl⟩
  refine ⟨?_, π ⬝ s, ?_, (Equiv.subtypeEquivRight ?_).trans (e.perm π), ?_, ?_⟩
  · intro x' hx' a ha
    have := h (π⁻¹ ⬝ x') (by simpa only [inv_perm_perm] using hx'.perm π⁻¹) (π⁻¹ a)
      (by simpa only [supp_perm_eq, Finset.mem_perm, perm_name_eq] using ha)
    simp only [supp_perm_eq, Finset.mem_perm, _root_.inv_inv, perm_name_eq, apply_inv_self] at this
    obtain this | this := this
    · exact Or.inl this
    · right
      rw [← perm_name_eq, ← Finset.mem_perm, ← supp_perm_eq,
        apply_perm_eq hf, SepProd.perm_def] at this
      simp only [perm_inv_perm] at this
      exact this
  · rw [Finset.disjoint_iff_ne] at hs ⊢
    rintro a ha _ ha' rfl
    simp only [supp_perm_eq, Finset.mem_union, Finset.mem_perm, perm_name_eq] at hs ha ha'
    exact hs _ ha _ ha' rfl
  · intro a
    simp only [supp_perm_eq, Finset.mem_inter, Finset.mem_perm]
  · simp only [fresh_def, supp_perm_eq, Finset.disjoint_iff_ne, Finset.mem_perm, swaps_inv,
      perm_name_eq, ne_eq, Finset.forall_mem_not_eq] at hx ⊢
    rintro a h₁ _ h₂ rfl
    by_cases hax : π⁻¹ a ∈ supp 𝔸 y
    · have ha : a ∈ supp 𝔸 (π ⬝ y) ∩ supp 𝔸 (π ⬝ x) := by
        simp only [supp_perm_eq, Finset.mem_inter, Finset.mem_perm,
          perm_name_eq, hax, h₂, and_self]
      rw [swaps_eq_of_mem₁ _ ha] at h₁
      simp only [Equiv.trans_apply] at h₁
      rw [← perm_name_eq, ← Finset.mem_perm] at h₁
      have := Finset.mem_inter_of_mem h₁ (((e.perm π) _).prop)
      rw [Finset.disjoint_union_left, Finset.disjoint_iff_inter_eq_empty] at hs
      rw [Finset.mem_inter, Finset.mem_perm, Finset.mem_perm, ← Finset.mem_inter, hs.1] at this
      exact Finset.not_mem_empty _ this
    · rw [swaps_eq_of_not_mem] at h₁
      contradiction
      · simp only [supp_perm_eq, Finset.mem_inter, Finset.mem_perm, perm_name_eq, hax, h₂,
          and_true, not_false_eq_true]
      · simp only [Finset.mem_perm, perm_name_eq]
        simp only [Finset.disjoint_iff_ne, Finset.mem_union, ne_eq, Finset.forall_mem_not_eq] at hs
        exact hs _ (Or.inr h₂)
  · rw [apply_perm_eq hf, SepProd.perm_def]
    congr 2
    dsimp only
    rw [← mul_perm, ← mul_perm]
    apply (Nominal.supp_supports 𝔸 y).perm_eq_perm
    intro a hay
    rw [coe_mul, coe_mul, Function.comp_apply, Function.comp_apply]
    by_cases hax : a ∈ supp 𝔸 x
    · rw [swaps_eq_of_mem₁, swaps_eq_of_mem₁]
      · simp only [Equiv.perm, perm_name_eq, Equiv.trans_apply, Equiv.coe_fn_mk,
          Equiv.subtypeEquivRight_apply_coe, inv_apply_self]
      · simp only [supp_perm_eq, Finset.mem_inter, Finset.mem_perm, perm_name_eq, inv_apply_self,
          hay, hax, and_self]
      · simp only [Finset.mem_inter, hay, hax, and_self]
    · rw [swaps_eq_of_not_mem, swaps_eq_of_not_mem]
      · simp only [supp_perm_eq, Finset.mem_inter, Finset.mem_perm, perm_name_eq, inv_apply_self,
          hax, and_false, not_false_eq_true]
      · simp only [Finset.mem_perm, perm_name_eq, inv_apply_self]
        rw [Finset.disjoint_iff_ne] at hs
        simp only [Finset.mem_union, ne_eq, Finset.forall_mem_not_eq] at hs
        exact hs a (Or.inl hay)
      · simp only [Finset.mem_inter, hax, and_false, not_false_eq_true]
      · rw [Finset.disjoint_iff_ne] at hs
        simp only [Finset.mem_union, ne_eq, Finset.forall_mem_not_eq] at hs
        exact hs a (Or.inl hay)

theorem transpAux_equivariant [Infinite 𝔸] [MulPerm 𝔸 α] [Nominal 𝔸 β] [MulPerm 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) :
    Equivariant 𝔸 (transpAux f) := by
  intro π
  ext y x z
  simp only [Function.perm_def, IsDiscrete.perm_eq]
  constructor
  · have := transpAux_equivariant' f hf (π⁻¹ ⬝ y) (π⁻¹ ⬝ x) (π⁻¹ ⬝ z) π
    rwa [perm_inv_perm, perm_inv_perm, perm_inv_perm] at this
  · exact transpAux_equivariant' f hf y x z π⁻¹

theorem supports_transpAux [Infinite 𝔸] [MulPerm 𝔸 α] [Nominal 𝔸 β] [MulPerm 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) :
    Supports (supp 𝔸 y) (transpAux f y) := by
  have := (transpAux_equivariant f hf).empty_supports
  have := this.apply (Nominal.supp_supports 𝔸 y)
  simp_rw [Finset.empty_union] at this
  exact this

theorem transpAux_coinjective [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) :
    Coinjective (transpAux f y) := by
  constructor
  intro z₁ z₂ x h₁ h₂
  obtain ⟨h, s, hs, e, he, rfl⟩ := h₁
  obtain ⟨-, s', hs', e', -, rfl⟩ := h₂
  rw [Finset.disjoint_union_left] at hs hs'
  obtain ⟨π, hπ₁, hπ₂⟩ := exists_extension (e.symm.trans e')
  have := apply_perm_eq hf π ⟨_, x, he⟩
  rw [perm_eq_of_fresh] at this
  · rw [this, SepProd.perm_def]
    congr 2
    · dsimp only
      rw [← inv_perm_eq_iff, swaps_inv, ← mul_perm, ← mul_perm]
      apply Nominal.supp_supports
      intro a hay
      simp only [coe_mul, Function.comp_apply]
      by_cases hax : a ∈ supp 𝔸 x
      · rw [swaps_eq_of_mem₁ a (Finset.mem_inter_of_mem hay hax),
          hπ₁ _ (Finset.coe_mem _), Equiv.trans_apply, Equiv.symm_apply_apply,
          swaps_eq_of_mem₂ _ (Finset.coe_mem _), Equiv.symm_apply_apply]
      · rw [Finset.disjoint_iff_ne, Finset.disjoint_iff_ne] at hs hs'
        have has := (hs.1 a hay a).mt (· rfl)
        have has' := (hs'.1 a hay a).mt (· rfl)
        have := (hπ₂ (a := a)).mt
          (λ h ↦ by simp only [Finset.mem_union, has, has', or_self] at h)
        rw [Finperm.mem_support_iff, not_not] at this
        rw [swaps_eq_of_not_mem a, this, swaps_eq_of_not_mem]
        · simp only [Finset.mem_inter, hax, and_false, not_false_eq_true]
        · exact has'
        · simp only [Finset.mem_inter, hax, and_false, not_false_eq_true]
        · exact has
    · rw [perm_eq_of_fresh]
      rw [fresh_def, Finperm.supp_eq]
      apply Disjoint.mono_left hπ₂
      rw [Finset.disjoint_union_left]
      exact ⟨hs.2.symm, hs'.2.symm⟩
  · rw [fresh_def, Finperm.supp_eq]
    apply Disjoint.mono_left hπ₂
    rw [Finset.disjoint_iff_ne]
    rintro a ha _ ha' rfl
    have hax : a ∉ supp 𝔸 x := by
      intro h
      rw [Finset.mem_union] at ha
      rw [Finset.disjoint_iff_ne, Finset.disjoint_iff_ne] at hs hs'
      obtain ha | ha := ha
      · exact hs.2 a h a ha rfl
      · exact hs'.2 a h a ha rfl
    have hax' := h ((swaps _ e)⁻¹ ⬝ x) ((perm_fresh_iff_fresh_inv_perm _ _ _).mp he)
      ((swaps (Disjoint.mono_left Finset.inter_subset_union ‹_›) e)⁻¹ ⬝ a)
    rw [← Finset.mem_perm, ← Finset.mem_perm, ← Finset.mem_perm,
      supp_perm_eq, perm_inv_perm, ← supp_perm_eq (f _), apply_perm_eq hf,
      SepProd.perm_def] at hax'
    simp only [hax, perm_inv_perm, ha', not_true_eq_false, or_self, imp_false] at hax'
    have hay := supp_apply_subset _ hf _ ha'
    simp only [SepProd.supp_eq, supp_perm_eq, Finset.mem_union, hax, or_false] at hay
    suffices hay : a ∈ supp 𝔸 y by
      have := Finset.disjoint_union_right.mpr ⟨hs.1, hs'.1⟩
      rw [Finset.disjoint_iff_ne] at this
      exact this a hay a ha rfl
    rw [Finset.mem_perm, swaps_inv, perm_name_eq] at hax' hay
    by_cases has : a ∈ s
    · rw [swaps_eq_of_mem₂ _ has] at hax' hay
      have := (e.symm ⟨a, has⟩).prop
      rw [Finset.mem_inter] at this
      cases hax' this.2
    · rwa [swaps_eq_of_not_mem] at hay
      · simp only [Finset.mem_inter, hax, and_false, not_false_eq_true]
      · exact has

theorem transpAux_of_fresh [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) (x : α) (h : y #[𝔸] x) :
    transpAux f y x (f ⟨y, x, h⟩) := by
  refine ⟨?_, ∅, λ ⦃_⦄ _ ↦ id, ?_, ?_, ?_⟩
  · intro x' hx' b hbx
    have hby : b ∉ supp 𝔸 y := by
      intro hby
      rw [fresh_def, Finset.disjoint_iff_ne] at h
      exact h b hby b hbx rfl
    rw [← imp_iff_or_not]
    intro hbf
    have := supp_apply_subset f hf _ hbf
    simp only [SepProd.supp_eq, Finset.mem_union, hby, false_or] at this
    exact this
  · apply Finset.equivOfCardEq
    simp only [Finset.card_empty, Finset.card_eq_zero, ← Finset.disjoint_iff_inter_eq_empty]
    exact h
  · rwa [perm_eq_of_fresh]
    rw [fresh_def, Finset.disjoint_iff_inter_eq_empty] at h
    rw [fresh_def, Finperm.supp_eq, swaps_support, h, Finset.union_idempotent]
    exact Finset.disjoint_empty_left _
  · congr 2
    rw [perm_eq_of_fresh]
    rw [fresh_def, Finset.disjoint_iff_inter_eq_empty] at h
    rw [fresh_def, Finperm.supp_eq, swaps_support, h, Finset.union_idempotent]
    exact Finset.disjoint_empty_left _

theorem supp_subset_union_of_transpAux [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    {f : β ∗[𝔸] α → γ} (hf : Equivariant 𝔸 f) {y : β} {x : α} {z : γ} :
    transpAux f y x z → supp 𝔸 z ⊆ supp 𝔸 y ∪ supp 𝔸 x := by
  intro h
  apply supp_minimal
  have := (supports_transpAux f hf y).apply (Nominal.supp_supports 𝔸 x)
  intro π hπ
  have := this π hπ
  have h' := h
  rw [← this, Function.perm_def, IsDiscrete.perm_eq] at h'
  rw [perm_eq_iff_eq_inv_perm]
  exact (transpAux_coinjective f hf y).coinjective h h'

theorem transp_mem_supp_iff_aux [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) (a : 𝔸) :
    (∃ x z, transpAux f y x z ∧ a ∈ supp 𝔸 z \ supp 𝔸 x) ↔
      ∃ x h, a ∈ supp 𝔸 (f ⟨y, x, h⟩) \ supp 𝔸 x := by
  constructor
  · rintro ⟨x, z, h, ha⟩
    have hz' := supp_subset_union_of_transpAux hf h
    obtain ⟨hz, s, hs, e, he, rfl⟩ := h
    have hs' := hs.mono_left Finset.inter_subset_union
    refine ⟨swaps hs' e ⬝ x, ?_, ?_⟩
    · have := he.perm (swaps hs' e)
      rwa [← mul_perm, swaps_swaps, one_perm] at this
    have hs : a ∉ s := by
      rw [Finset.mem_sdiff] at ha
      have := hz' ha.1
      rw [Finset.disjoint_iff_ne] at hs
      exact (hs a this a).mt (· rfl)
    have := Finset.perm_mem_perm ha (swaps hs' e)
    rw [perm_name_eq, Finset.perm_sdiff, swaps_eq_of_not_mem] at this
    · simp only [Finset.mem_sdiff, ← supp_perm_eq, apply_perm_eq hf,
        SepProd.perm_def, ← mul_perm, swaps_swaps, one_perm] at this ⊢
      exact this
    · rw [Finset.mem_sdiff] at ha
      simp only [Finset.mem_inter, ha.2, and_false, not_false_eq_true]
    · exact hs
  · rintro ⟨x, h, ha⟩
    exact ⟨x, f ⟨y, x, h⟩, transpAux_of_fresh f hf y x h, ha⟩

theorem transp_mem_supp_of [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) (a : 𝔸) :
    (∃ x z, transpAux f y x z ∧ a ∈ supp 𝔸 z \ supp 𝔸 x) →
    a ∈ supp 𝔸 (transpAux f y) := by
  rintro ⟨x, z, hz, ha⟩
  rw [Finset.mem_sdiff] at ha
  rw [mem_supp_iff_names_infinite _ ⟨_, supports_transpAux _ hf _⟩]
  have := (supp 𝔸 (transpAux f y) ∪ supp 𝔸 x ∪ supp 𝔸 z).finite_toSet
  apply (Set.Finite.infinite_compl this).mono
  intro b hb
  simp only [Finset.coe_union, Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff,
    Finset.mem_coe] at hb
  intro h
  have hz' := (congr_fun₂ h x z).mpr hz
  rw [Function.perm_def, swap_inv, Function.perm_def, swap_inv, IsDiscrete.perm_eq] at hz'
  have : swap a b ⬝ x = x := by
    apply Nominal.supp_supports 𝔸 x
    intro c hc
    rw [swap_apply_of_ne_of_ne]
    · rintro rfl
      exact ha.2 hc
    · rintro rfl
      exact hb.1.2 hc
  rw [this] at hz'
  have := congr_arg (a ∈ supp 𝔸 ·) ((transpAux_coinjective f hf y).coinjective hz hz')
  simp only [ha.1, supp_perm_eq, Finset.mem_perm, swap_inv, perm_name_eq, swap_apply_left, hb.2,
    eq_iff_iff, iff_false, not_true_eq_false] at this

/-! ̄a_y = {a | ∃ x h, a ∈ supp 𝔸 (f ⟨y, x, h⟩) \ supp 𝔸 x}. -/

theorem transp_mem_supp_iff_aux'' [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (y : β) (x : α) (z : γ) (a b : 𝔸)
    (ha' : ∀ x h, a ∉ supp 𝔸 (f ⟨y, x, h⟩) \ supp 𝔸 x)
    (hb' : ∀ x h, b ∉ supp 𝔸 (f ⟨y, x, h⟩) \ supp 𝔸 x) :
    (swap a b ⬝ transpAux f y) x z → x ∈ dom (transpAux f y) := by
  rintro ⟨hy, s, hs, e, he, hz⟩
  rw [transpAux_dom_eq]
  intro x' hx' c hc
  specialize ha' x' hx'
  specialize hb' x' hx'
  simp only [Finset.mem_sdiff, not_and, Decidable.not_not] at ha' hb'
  by_cases hac : a = c
  · cases hac
    by_cases h : a ∈ supp 𝔸 (f ⟨y, x', hx'⟩)
    · exact Or.inl (ha' h)
    · exact Or.inr h
  by_cases hbc : b = c
  · cases hbc
    by_cases h : b ∈ supp 𝔸 (f ⟨y, x', hx'⟩)
    · exact Or.inl (hb' h)
    · exact Or.inr h
  · have := hy x' hx' (swap a b ⬝ c)
    apply hy x' hx' c
    rwa [supp_perm_eq, Finset.mem_perm, _root_.inv_inv, perm_name_eq,
      swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]

theorem transp_mem_supp_iff_aux' [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) (x : α) (z : γ)
    (a b : 𝔸) (ha : a ∈ supp 𝔸 y) (hb : b ∉ supp 𝔸 y)
    (ha' : ∀ x h, a ∉ supp 𝔸 (f ⟨y, x, h⟩) \ supp 𝔸 x)
    (hb' : ∀ x h, b ∉ supp 𝔸 (f ⟨y, x, h⟩) \ supp 𝔸 x)
    (hab : a ≠ b) :
    (swap a b ⬝ transpAux f y) x z → transpAux f y x z := by
  intro h
  have hx := transp_mem_supp_iff_aux'' f y x z a b ha' hb' h
  rw [transpAux_dom_eq] at hx
  refine ⟨hx, ?_⟩
  rw [apply_perm_eq (transpAux_equivariant f hf)] at h
  obtain ⟨hy, s, hs, e, he, rfl⟩ := h
  have hs' := hs.mono_left Finset.inter_subset_union
  have hbs : b ∉ s := by
    simp only [supp_perm_eq, Finset.disjoint_iff_ne, Finset.mem_union, Finset.mem_perm, swap_inv,
      perm_name_eq, ne_eq, Finset.forall_mem_not_eq] at hs
    apply hs
    simp only [swap_apply_right, ha, true_or]
  rw [perm_fresh_iff_fresh_inv_perm, perm_fresh_iff_fresh_inv_perm, swaps_inv, swap_inv] at he
  have haf : a ∉ supp 𝔸 (f ⟨y, swap a b ⬝ swaps hs' e ⬝ x, he⟩) := by
    specialize ha' _ he
    rw [Finset.mem_sdiff, not_and'] at ha'
    apply ha'
    intro ha''
    rw [fresh_def, Finset.disjoint_iff_ne] at he
    exact he a ha a ha'' rfl
  sorry

theorem transp_mem_supp_iff [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) (a : 𝔸) :
    a ∈ supp 𝔸 (transpAux f y) ↔
      ∃ x z, transpAux f y x z ∧ a ∈ supp 𝔸 z \ supp 𝔸 x := by
  refine ⟨?_, transp_mem_supp_of f hf y a⟩
  rw [transp_mem_supp_iff_aux f hf]
  contrapose!
  intro ha
  by_cases ha' : a ∈ supp 𝔸 y
  swap
  · contrapose! ha'
    exact supp_minimal _ _ (supports_transpAux f hf y) ha'
  rw [mem_supp_iff_names_infinite _ ⟨_, supports_transpAux _ hf _⟩, Set.not_infinite]
  apply (supp 𝔸 y ∪ {a}).finite_toSet.subset
  intro b hb
  contrapose! hb
  simp only [Finset.coe_union, Finset.coe_singleton, Set.union_singleton, Set.mem_insert_iff,
    Finset.mem_coe, not_or] at hb
  have hb' : ∀ x h, b ∉ supp 𝔸 (f ⟨y, x, h⟩) \ supp 𝔸 x := by
    intro x hx hb'
    rw [Finset.mem_sdiff] at hb'
    have := supp_apply_subset f hf _ hb'.1
    simp only [SepProd.supp_eq, Finset.mem_union, hb.2, hb'.2, or_self] at this
  simp only [ne_eq, Set.mem_setOf_eq, not_not]
  ext x z
  constructor
  · exact transp_mem_supp_iff_aux' f hf y x z a b ha' hb.2 ha hb' (Ne.symm hb.1)
  · simp only [Function.perm_def, swap_inv, IsDiscrete.perm_eq]
    have := transp_mem_supp_iff_aux' f hf y (swap a b ⬝ x) (swap a b ⬝ z)
      a b ha' hb.2 ha hb' (Ne.symm hb.1)
    simp only [Function.perm_def, swap_inv, ← mul_perm, swap_swap, one_perm,
      IsDiscrete.perm_eq] at this
    exact this

theorem transp_mem_dom_iff [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) (x : α) :
    x ∈ dom (transpAux f y) ↔ x #[𝔸] transpAux f y := by
  rw [transpAux_dom_eq, fresh_def, Finset.disjoint_iff_ne]
  simp only [transp_mem_supp_iff f hf, transp_mem_supp_iff_aux f hf]
  constructor
  · rintro h a ha b ⟨x', hx, hb⟩ rfl
    rw [Finset.mem_sdiff] at hb
    have := h x' hx a
    simp only [ha, hb.2, hb.1, not_true_eq_false, or_self, imp_false] at this
  · intro h x' hx b hb
    by_contra hb'
    simp only [not_or, Decidable.not_not] at hb'
    have := h b hb b
    simp only [Finset.mem_sdiff, exists_and_right, ne_eq, not_true_eq_false, imp_false, not_exists,
      not_and, Decidable.not_not, forall_exists_index] at this
    have := this x' hx
    simp only [hb'.2, hb'.1, imp_false, not_true_eq_false] at this

/-- The transpose of an equivariant function `β ∗ α → γ` across the adjunction,
giving an equivariant function `β → (α -∗ γ)`. -/
def transp [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) :
    α -∗[𝔸] γ where
  rel := transpAux f y
  rel_fs := ⟨_, supports_transpAux f hf y⟩
  rel_coinjective := transpAux_coinjective f hf y
  mem_dom_iff := transp_mem_dom_iff f hf y
  mem_supp_iff := transp_mem_supp_iff f hf y

end SepImp
