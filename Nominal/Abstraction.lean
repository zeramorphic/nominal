import Nominal.Instances
import Nominal.Quantifier

open Finperm

variable {𝔸 α β γ : Type*} [DecidableEq 𝔸] [Infinite 𝔸]

structure Abstract' (𝔸 α β : Type*) where
  param : α
  val : β

namespace Abstract'

variable [MulPerm 𝔸 α] [MulPerm 𝔸 β]

instance : HasPerm 𝔸 (Abstract' 𝔸 α β) where
  perm π x := ⟨π ⬝ x.param, π ⬝ x.val⟩

omit [Infinite 𝔸] in
theorem perm_def (π : Finperm 𝔸) (x : Abstract' 𝔸 α β) :
    π ⬝ x = ⟨π ⬝ x.param, π ⬝ x.val⟩ :=
  rfl

instance : MulPerm 𝔸 (Abstract' 𝔸 α β) where
  one_perm := by
    rintro ⟨p, v⟩
    rw [perm_def, one_perm, one_perm]
  mul_perm := by
    rintro π₁ π₂ ⟨p, v⟩
    rw [perm_def, mul_perm, mul_perm]
    rfl

def Rel (x y : Abstract' 𝔸 α β) : Prop :=
  ∃ π : Finperm 𝔸, π ⬝ x = y ∧ π #[𝔸] supp 𝔸 x.val \ supp 𝔸 x.param

omit [Infinite 𝔸] in
theorem perm_supp_diff_eq (π : Finperm 𝔸) (x : Abstract' 𝔸 α β) :
    π ⬝ (supp 𝔸 x.val \ supp 𝔸 x.param) = supp 𝔸 (π ⬝ x).val \ supp 𝔸 (π ⬝ x).param := by
  ext a
  rw [Finset.perm_def]
  simp only [perm_def, supp_perm_eq, Finset.mem_sdiff, Finset.mem_perm, perm_name_eq,
    Finset.mem_map, Function.Embedding.coeFn_mk]
  aesop

theorem perm_supp_diff_eq' {π : Finperm 𝔸} {x : Abstract' 𝔸 α β}
    (h : π #[𝔸] (supp 𝔸 x.val \ supp 𝔸 x.param)) :
    supp 𝔸 (π ⬝ x).val \ supp 𝔸 (π ⬝ x).param = supp 𝔸 x.val \ supp 𝔸 x.param := by
  rw [← perm_supp_diff_eq, perm_eq_of_fresh h]

theorem rel_refl (x : Abstract' 𝔸 α β) :
    Rel x x := by
  use 1
  simp only [one_perm, fresh_iff, coe_one, id_eq, implies_true, and_self]

theorem rel_symm {x y : Abstract' 𝔸 α β} (h : Rel x y) :
    Rel y x := by
  obtain ⟨π, rfl, hπ⟩ := h
  refine ⟨π⁻¹, inv_perm_perm π x, ?_⟩
  rwa [perm_supp_diff_eq' hπ, fresh_def, Finperm.supp_eq, inv_support,
    ← Finperm.supp_eq, ← fresh_def]

theorem rel_trans {x y z : Abstract' 𝔸 α β} (h₁ : Rel x y) (h₂ : Rel y z) :
    Rel x z := by
  obtain ⟨π₁, rfl, hπ₁⟩ := h₁
  obtain ⟨π₂, rfl, hπ₂⟩ := h₂
  refine ⟨π₂ * π₁, mul_perm π₂ π₁ x, ?_⟩
  rw [perm_supp_diff_eq' hπ₁] at hπ₂
  rw [fresh_def, Finperm.supp_eq, Finset.disjoint_iff_ne] at hπ₁ hπ₂ ⊢
  intro a ha
  have := mul_support_subset π₂ π₁ ha
  rw [Finset.mem_union] at this
  obtain (h | h) := this
  · exact hπ₂ a h
  · exact hπ₁ a h

theorem rel_equivalence :
    Equivalence (Rel : Abstract' 𝔸 α β → Abstract' 𝔸 α β → Prop) :=
  ⟨rel_refl, rel_symm, rel_trans⟩

theorem rel_perm {x y : Abstract' 𝔸 α β} (h : Rel x y) (π : Finperm 𝔸) :
    Rel (π ⬝ x) (π ⬝ y) := by
  obtain ⟨π', rfl, hπ'⟩ := h
  refine ⟨π ⬝ π', ?_, ?_⟩
  · simp only [Finperm.perm_def, mul_perm, inv_perm_perm]
  rw [← perm_supp_diff_eq]
  exact hπ'.perm π

instance setoid : Setoid (Abstract' 𝔸 α β) where
  r := Rel (𝔸 := 𝔸)
  iseqv := rel_equivalence

end Abstract'

theorem Abstract'.rel_iff_aux [Nominal 𝔸 α] [Nominal 𝔸 β]
    {x y : Abstract' 𝔸 α β} (π : Finperm 𝔸)
    (hπ₁ : π ⬝ x = y) (hπ₂ : π #[𝔸] supp 𝔸 x.val \ supp 𝔸 x.param) :
    ∃ π : Finperm 𝔸, π ⬝ x = y ∧
      π #[𝔸] supp 𝔸 x.val \ supp 𝔸 x.param ∧
      π.support ⊆ supp 𝔸 x.param ∪ supp 𝔸 y.param := by
  cases hπ₁
  have hπ : (supp 𝔸 x.param).image π = supp 𝔸 (π ⬝ x).param := by
    ext a
    simp only [Finset.mem_image, perm_def, supp_perm_eq, Finset.mem_perm, perm_name_eq]
    aesop
  obtain ⟨π', hπ'₁, hπ'₂⟩ := exists_extension
    (π.toPerm (supp 𝔸 x.param) (supp 𝔸 (π ⬝ x).param) hπ)
  refine ⟨π', ?_, ?_, hπ'₂⟩
  · have := Nominal.supp_supports 𝔸 (x.param, x.val) (π'⁻¹ * π) ?_
    · simp only [mul_perm, Prod.perm_mk, Prod.mk.injEq, inv_perm_eq_iff] at this
      cases x
      rw [perm_def, perm_def, mk.injEq, this.1, this.2]
      exact ⟨rfl, rfl⟩
    intro a ha
    simp only [coe_mul, Function.comp_apply, inv_apply_eq_iff_eq]
    simp only [Prod.supp_mk, Finset.mem_union] at ha
    by_cases ha' : a ∈ supp 𝔸 x.param
    · have := hπ'₁ a ha'
      simp only [toPerm_apply] at this
      rw [this]
    · simp only [ha', false_or] at ha
      simp only [fresh_iff, Finset.names_supp_eq, Finset.mem_sdiff, and_imp] at hπ₂
      rw [hπ₂ a ha ha', eq_comm]
      by_contra ha''
      rw [← ne_eq, ← Finperm.mem_support_iff] at ha''
      have := hπ'₂ ha''
      simp only [perm_def, supp_perm_eq, Finset.mem_union, ha', Finset.mem_perm, perm_name_eq,
        false_or] at this
      rw [← hπ₂ a ha ha', inv_apply_self] at this
      contradiction
  · simp only [fresh_iff, Finset.names_supp_eq, Finset.mem_sdiff, and_imp]
    intro a ha₁ ha₂
    by_contra ha₃
    rw [← ne_eq, ← Finperm.mem_support_iff] at ha₃
    have := hπ'₂ ha₃
    simp only [Finset.mem_union, ha₂, false_or] at this
    have h := hπ'₁ (π⁻¹ a) ?_
    · simp only [toPerm_apply, apply_inv_self] at h
      simp only [fresh_iff, Finset.names_supp_eq, Finset.mem_sdiff, and_imp] at hπ₂
      have := hπ₂ a
      simp only [ha₁, ha₂, not_false_eq_true, forall_const] at this
      rw [eq_comm, ← inv_apply_eq_iff_eq] at this
      rw [this] at h
      rw [mem_support_iff] at ha₃
      contradiction
    · simp only [perm_def, supp_perm_eq, Finset.mem_perm, perm_name_eq] at this
      exact this

/-- A more powerful, but equivalent, definition of the relation. -/
theorem Abstract'.rel_iff [Nominal 𝔸 α] [Nominal 𝔸 β] (x y : Abstract' 𝔸 α β) :
    Rel x y ↔ ∃ π : Finperm 𝔸, π ⬝ x = y ∧
      π #[𝔸] supp 𝔸 x.val \ supp 𝔸 x.param ∧
      π.support ⊆ supp 𝔸 x.param ∪ supp 𝔸 y.param := by
  constructor
  · rintro ⟨π, hπ₁, hπ₂⟩
    exact rel_iff_aux π hπ₁ hπ₂
  · rintro ⟨π, rfl, hπ⟩
    exact ⟨π, rfl, hπ.1⟩

def Abstract (𝔸 α β : Type*) [DecidableEq 𝔸] [Infinite 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] :=
  Quotient (Abstract'.setoid (𝔸 := 𝔸) (α := α) (β := β))

namespace Abstract
open Abstract'

section Basic

variable [MulPerm 𝔸 α] [MulPerm 𝔸 β]

notation:max "["α"|"𝔸"]" β:max => Abstract 𝔸 α β

def mk (param : α) (val : β) : [α|𝔸]β :=
  Quotient.mk Abstract'.setoid ⟨param, val⟩

notation "⟨"param"⟩" val:max => Abstract.mk param val

theorem sound {x₁ x₂ : α} {y₁ y₂ : β} (h : Rel (𝔸 := 𝔸) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩) :
    (⟨x₁⟩y₁ : [α|𝔸]β) = ⟨x₂⟩y₂ :=
  Quotient.sound h

def lift {γ : Sort*} (f : α → β → γ)
    (hf : ∀ (x₁ x₂ : α) (y₁ y₂ : β), Rel (𝔸 := 𝔸) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ → f x₁ y₁ = f x₂ y₂) :
    [α|𝔸]β → γ :=
  Quotient.lift (λ x ↦ f x.param x.val) (λ x y ↦ hf x.param y.param x.val y.val)

theorem ind {motive : [α|𝔸]β → Prop} (mk : ∀ x y, motive (⟨x⟩y)) :
    ∀ x, motive x :=
  Quotient.ind (λ x ↦ mk x.param x.val)

theorem exact {x₁ x₂ : α} {y₁ y₂ : β} (h : (⟨x₁⟩y₁ : [α|𝔸]β) = ⟨x₂⟩y₂) :
    Rel (𝔸 := 𝔸) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ :=
  Quotient.exact h

theorem mk_eq_iff {x₁ x₂ : α} {y₁ y₂ : β} :
    (⟨x₁⟩y₁ : [α|𝔸]β) = ⟨x₂⟩y₂ ↔ Rel (𝔸 := 𝔸) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ :=
  ⟨exact, sound⟩

/-!
# Nominal structure
-/

theorem perm_aux (π : Finperm 𝔸) (x₁ x₂ : α) (y₁ y₂ : β) (h : Rel (𝔸 := 𝔸) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩) :
    (⟨π ⬝ x₁⟩(π ⬝ y₁) : [α|𝔸]β) = ⟨π ⬝ x₂⟩(π ⬝ y₂) := by
  rw [mk_eq_iff]
  exact rel_perm h π

instance : HasPerm 𝔸 [α|𝔸]β where
  perm π := lift (λ x y ↦ ⟨π ⬝ x⟩(π ⬝ y)) (perm_aux π)

@[simp]
theorem perm_mk (π : Finperm 𝔸) (x : α) (y : β) :
    π ⬝ (⟨x⟩y : [α|𝔸]β) = ⟨π ⬝ x⟩(π ⬝ y) :=
  rfl

instance : MulPerm 𝔸 [α|𝔸]β where
  one_perm x := by
    induction x using ind
    case mk x y => simp only [perm_mk, one_perm]
  mul_perm π₁ π₂ x := by
    induction x using ind
    case mk x y => simp only [perm_mk, mul_perm]

end Basic

theorem supports_mk [Nominal 𝔸 α] [Nominal 𝔸 β] (x : α) (y : β) :
    Supports (supp 𝔸 y \ supp 𝔸 x) (⟨x⟩y : [α|𝔸]β) := by
  intro π hπ
  rw [perm_mk, mk_eq_iff]
  rw [← Abstract'.perm_def π ⟨x, y⟩]
  refine ⟨π⁻¹, ?_, ?_⟩
  · simp only [inv_perm_perm]
  · rw [← perm_supp_diff_eq, fresh_perm_iff_inv_perm_fresh, Finperm.fresh_iff]
    intro b hb
    rw [Finset.names_supp_eq] at hb
    rw [Finperm.perm_def, inv_inv, inv_mul_cancel_right, inv_apply_eq_iff_eq, hπ b hb]

theorem subset_of_supports [Nominal 𝔸 α] [Nominal 𝔸 β] {x : α} {y : β} {s : Finset 𝔸}
    (hs : Supports s (⟨x⟩y : [α|𝔸]β)) :
    supp 𝔸 y \ supp 𝔸 x ⊆ s := by
  intro a ha
  rw [Finset.mem_sdiff] at ha
  by_contra ha'
  obtain ⟨b, hb₁, hb₂, hb₃,hb₄⟩ := ((newNames_not_mem (supp 𝔸 y)).and
    ((newNames_not_mem (supp 𝔸 x)).and ((newNames_not_mem s).and (newNames_not_mem {a})))).exists
  rw [Finset.mem_singleton] at hb₄
  have := hs (swap a b) ?_
  · rw [perm_mk, mk_eq_iff] at this
    obtain ⟨π, hπ₁, hπ₂⟩ := this
    simp only [Abstract'.perm_def, Abstract'.mk.injEq] at hπ₁
    simp only [supp_perm_eq, fresh_iff, Finset.names_supp_eq, Finset.mem_sdiff, and_imp] at hπ₂
    have := congr_arg (a ∈ supp 𝔸 ·) hπ₁.2
    simp only [supp_perm_eq, Finset.mem_perm, perm_name_eq, swap_inv, ha.1, eq_iff_iff,
      iff_true] at this
    have ha'' := hπ₂ (π⁻¹ a) ?_ ?_
    · simp only [apply_inv_self] at ha''
      rw [← ha'', swap_apply_left] at this
      contradiction
    · rwa [Finset.mem_perm, swap_inv, perm_name_eq]
    · rw [← perm_name_eq, ← Finset.mem_perm, ← supp_perm_eq, ← supp_perm_eq, hπ₁.1]
      exact ha.2
  · intro c hc
    rw [swap_apply_of_ne_of_ne] <;>
    · rintro rfl; contradiction

instance [Nominal 𝔸 α] [Nominal 𝔸 β] : Nominal 𝔸 [α|𝔸]β where
  supported x := by
    induction x using ind
    case mk x y =>
    exact ⟨_, supports_mk _ _⟩

@[simp]
protected theorem supp_eq [Nominal 𝔸 α] [Nominal 𝔸 β] (x : α) (y : β) :
    supp 𝔸 (⟨x⟩y : [α|𝔸]β) = supp 𝔸 y \ supp 𝔸 x := by
  apply subset_antisymm
  · apply supp_minimal
    exact supports_mk x y
  · apply subset_of_supports
    exact Nominal.supp_supports 𝔸 (⟨x⟩y)

/-- An induction principle for `[α|𝔸]β`. -/
theorem fresh_induction [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ] {motive : [α|𝔸]β → Prop}
    (t : γ) (h : ∀ x y, x #[𝔸] t → motive (⟨x⟩y)) (x : [α|𝔸]β) : motive x := by
  induction x using ind
  case mk x y =>
  obtain ⟨π, hπ₁, hπ₂⟩ := Finperm.exists_fresh (supp 𝔸 x) (supp 𝔸 t ∪ supp 𝔸 y)
  have := h (π ⬝ x) (π ⬝ y) ?_
  · convert this using 1
    rw [mk_eq_iff]
    refine ⟨π, rfl, ?_⟩
    aesop
  · rw [fresh_def, supp_perm_eq, Finset.disjoint_iff_ne]
    rintro a ha₁ _ ha₂ rfl
    rw [Finset.mem_perm, perm_name_eq] at ha₁
    have := hπ₁ (π⁻¹ a) ha₁
    aesop

/-!
# Functoriality
-/

theorem exists_map [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β → γ) (hf : FinitelySupported 𝔸 f) (x : [α|𝔸]β) :
    ∃ y : [α|𝔸]γ, ∀ a b, a #[𝔸] f → x = ⟨a⟩b → y = ⟨a⟩(f b) := by
  induction x using fresh_induction f
  infer_instance
  case h x y hxy =>
  use ⟨x⟩(f y)
  intro x' y' hxy' h
  rw [mk_eq_iff] at h ⊢
  rw [Abstract'.rel_iff] at h
  obtain ⟨π, hπ₁, hπ₂, hπ₃⟩ := h
  cases hπ₁
  dsimp only at *
  have hfy := congr_fun (supp_supports' f hf π ?_) (π ⬝ y)
  swap
  · intro a ha
    by_contra ha'
    rw [← ne_eq, ← mem_support_iff] at ha'
    have := hπ₃ ha'
    simp only [fresh_def, supp_perm_eq, Finset.disjoint_iff_ne] at hxy hxy'
    aesop
  simp only [Function.perm_def, inv_perm_perm] at hfy
  refine ⟨π, ?_, ?_⟩
  · rw [Abstract'.perm_def, Abstract'.mk.injEq]
    simp only [hfy, and_self]
  · simp only [fresh_iff, Finset.names_supp_eq, Finset.mem_sdiff, and_imp]
    intro a ha ha'
    by_contra ha''
    simp only [fresh_iff, Finset.names_supp_eq, Finset.mem_sdiff, and_imp] at hπ₂
    have hay := hπ₂ a
    simp only [ha', not_false_eq_true, ha'', imp_false, not_true_eq_false] at hay
    rw [← ne_eq, ← mem_support_iff] at ha''
    have hax := hπ₃ ha''
    simp only [Finset.mem_union, ha', false_or] at hax
    rw [fresh_def, Finset.disjoint_iff_ne] at hxy'
    have := supp_apply_subset' f hf y ha
    simp only [Finset.mem_union] at this
    tauto

noncomputable def map [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β → γ) (hf : FinitelySupported 𝔸 f) (x : [α|𝔸]β) : [α|𝔸]γ :=
  (exists_map f hf x).choose

theorem map_mk [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    {f : β → γ} {hf : FinitelySupported 𝔸 f} {a : α} {b : β} (hab : a #[𝔸] f) :
    map f hf (⟨a⟩b) = ⟨a⟩(f b) :=
  (exists_map f hf (⟨a⟩b)).choose_spec a b hab rfl

end Abstract
