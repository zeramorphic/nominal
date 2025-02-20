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
-/

def transpAux [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (y : β) (x : α) (z : γ) : Prop :=
  (∀ x' : α, ∀ h, ∀ a ∈ supp 𝔸 x, a ∈ supp 𝔸 x' ∨ a ∉ supp 𝔸 (f ⟨y, x', h⟩)) ∧
  ∃ π : Finperm 𝔸,
    (∀ a, a ∈ supp 𝔸 y → a ∈ supp 𝔸 x → π a ∉ supp 𝔸 y ∧ π a ∉ supp 𝔸 x) ∧
    (∀ a, a ∈ supp 𝔸 y ∨ a ∈ supp 𝔸 x → a ∉ supp 𝔸 y ∨ a ∉ supp 𝔸 x → π a = a) ∧
    ∃ h, z = f ⟨π ⬝ y, x, h⟩

theorem transpAux_dom_eq [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (y : β) (x : α) :
    x ∈ Rel.dom (transpAux f y) ↔
    ∀ x' : α, ∀ h, ∀ a ∈ supp 𝔸 x, a ∈ supp 𝔸 x' ∨ a ∉ supp 𝔸 (f ⟨y, x', h⟩) := by
  simp only [dom, transpAux, Set.mem_setOf_eq, exists_and_left, and_iff_left_iff_imp]
  intro h
  obtain ⟨π, hπ₁, hπ₂⟩ := Finperm.exists_fresh (supp 𝔸 y ∩ supp 𝔸 x) (supp 𝔸 y ∪ supp 𝔸 x)
  suffices (π ⬝ y) #[𝔸] x by
    refine ⟨_, π, ?_, ?_, this, rfl⟩
    · simp only [Finset.mem_inter, Finset.mem_union, not_or, and_imp] at hπ₁
      exact hπ₁
    · simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, not_and_or, and_imp] at hπ₂
      exact hπ₂
  rw [fresh_def, Finset.disjoint_iff_ne]
  rintro a hay _ hax rfl
  rw [supp_perm_eq, Finset.mem_perm, perm_name_eq] at hay
  specialize hπ₁ (π⁻¹ a)
  simp only [Finset.mem_inter, hay, true_and, apply_inv_self, Finset.mem_union, hax, or_true,
    not_true_eq_false, imp_false] at hπ₁
  specialize hπ₂ (π⁻¹ a)
  simp only [Finset.mem_sdiff, Finset.mem_union, hay, hπ₁, or_false, Finset.mem_inter, and_false,
    not_false_eq_true, and_self, apply_inv_self, forall_const] at hπ₂
  rw [← hπ₂] at hπ₁
  contradiction

theorem transpAux_equivariant' [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) (x : α) (z : γ) (π : Finperm 𝔸) :
    transpAux f y x z → transpAux f (π ⬝ y) (π ⬝ x) (π ⬝ z) := by
  rintro ⟨h, π', h₁, h₂, h₃, rfl⟩
  refine ⟨?_, π * π' * π⁻¹, ?_, ?_, ?_, ?_⟩
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
  · intro a ha ha'
    simp only [supp_perm_eq, Finset.mem_perm, perm_name_eq] at ha ha'
    simp only [supp_perm_eq, coe_mul, Function.comp_apply, Finset.mem_perm, perm_name_eq,
      inv_apply_self]
    exact h₁ (π⁻¹ a) ha ha'
  · intro a ha ha'
    simp only [supp_perm_eq, Finset.mem_perm, perm_name_eq] at ha ha'
    simp only [coe_mul, Function.comp_apply]
    rw [← perm_name_eq _ (π' (π⁻¹ a)), perm_eq_iff_eq_inv_perm]
    exact h₂ (π⁻¹ a) ha ha'
  · simp only [mul_perm, inv_perm_perm]
    exact h₃.perm π
  · simp only [apply_perm_eq hf, SepProd.perm_def, mul_perm, inv_perm_perm]

theorem transpAux_equivariant [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
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

theorem transpAux_coinjective [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) :
    Rel.Coinjective (transpAux f y) := by
  constructor
  intro z₁ z₂ x h₁ h₂
  obtain ⟨h, π, hπ₁, hπ₂, hπ₃, rfl⟩ := h₁
  obtain ⟨h', π', hπ₁', hπ₂', hπ₃', rfl⟩ := h₂
  sorry

/-- The transpose of an equivariant function `β ∗ α → γ` across the adjunction,
giving an equivariant function `β → (α -∗ γ)`. -/
def transp [Infinite 𝔸] [MulPerm 𝔸 α] [Nominal 𝔸 β] [MulPerm 𝔸 γ]
    (f : β ∗[𝔸] α → γ) (hf : Equivariant 𝔸 f) (y : β) :
    α -∗[𝔸] γ where
  rel := transpAux f y
  rel_fs := ⟨_, supports_transpAux f hf y⟩
  rel_coinjective := transpAux_coinjective f hf y
  mem_dom_iff := sorry
  mem_supp_iff := sorry

end SepImp
