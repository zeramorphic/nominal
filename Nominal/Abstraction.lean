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
  ∃ π : Finperm 𝔸, π ⬝ x = y ∧ π #[𝔸] (supp 𝔸 x.2 \ supp 𝔸 x.1)

omit [Infinite 𝔸] in
theorem perm_supp_diff_eq (π : Finperm 𝔸) (x : Abstract' 𝔸 α β) :
    π ⬝ (supp 𝔸 x.2 \ supp 𝔸 x.1) = supp 𝔸 (π ⬝ x).2 \ supp 𝔸 (π ⬝ x).1 := by
  ext a
  rw [Finset.perm_def]
  simp only [perm_def, supp_perm_eq, Finset.mem_sdiff, Finset.mem_perm_iff, perm_name_eq,
    Finset.mem_map, Function.Embedding.coeFn_mk]
  aesop

theorem perm_supp_diff_eq' {π : Finperm 𝔸} {x : Abstract' 𝔸 α β}
    (h : π #[𝔸] (supp 𝔸 x.2 \ supp 𝔸 x.1)) :
    supp 𝔸 (π ⬝ x).2 \ supp 𝔸 (π ⬝ x).1 = supp 𝔸 x.2 \ supp 𝔸 x.1 := by
  rw [← perm_supp_diff_eq, perm_eq_of_fresh h]

theorem rel_refl (x : Abstract' 𝔸 α β) :
    Rel x x := by
  use 1
  simp only [one_perm, fresh_iff, coe_one, id_eq, implies_true, and_self]

theorem rel_symm {x y : Abstract' 𝔸 α β} (h : Rel x y) :
    Rel y x := by
  obtain ⟨π, rfl, hπ⟩ := h
  refine ⟨π⁻¹, inv_perm_perm π x, ?_⟩
  rwa [perm_supp_diff_eq' hπ, fresh_def, Finperm.supp_eq, inv_support, ← Finperm.supp_eq, ← fresh_def]

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
    simp only [supp_perm_eq, Finset.mem_perm_iff, perm_name_eq, swap_inv, ha.1, eq_iff_iff,
      iff_true] at this
    have ha'' := hπ₂ (π⁻¹ a) ?_ ?_
    · simp only [apply_inv_self] at ha''
      rw [← ha'', swap_apply_left] at this
      contradiction
    · rwa [Finset.mem_perm_iff, swap_inv, perm_name_eq]
    · rw [← perm_name_eq, ← Finset.mem_perm_iff, ← supp_perm_eq, ← supp_perm_eq, hπ₁.1]
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
    rw [Finset.mem_perm_iff, perm_name_eq] at ha₁
    have := hπ₁ (π⁻¹ a) ha₁
    aesop

theorem exists_map [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    (f : β → γ) (hf : FinitelySupported 𝔸 f) (x : [α|𝔸]β) :
    ∃ y : [α|𝔸]γ, ∀ a b, a #[𝔸] f → x = ⟨a⟩b → y = ⟨a⟩(f b) := by
  sorry

noncomputable def map [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    (f : β → γ) (hf : FinitelySupported 𝔸 f) (x : [α|𝔸]β) : [α|𝔸]γ :=
  (exists_map f hf x).choose

theorem map_mk [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    {f : β → γ} {hf : FinitelySupported 𝔸 f} {a : α} {b : β} (hab : a #[𝔸] f) :
    map f hf (⟨a⟩b) = ⟨a⟩(f b) :=
  (exists_map f hf (⟨a⟩b)).choose_spec a b hab rfl

end Abstract
