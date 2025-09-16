import Nominal.Basic

open Finperm

variable {𝔸 : Type*} [DecidableEq 𝔸]

theorem supp_equivariant [Infinite 𝔸] {α : Type*} [MulPerm 𝔸 α] :
    Equivariant 𝔸 (supp 𝔸 : α → Finset 𝔸) := by
  rw [Function.equivariant_iff]
  intro π x
  ext a
  rw [Finset.mem_perm]
  by_cases hx : FinitelySupported 𝔸 x
  · rw [mem_supp_iff' x hx, mem_supp_iff' (π ⬝ x) (hx.perm π)]
    constructor
    · intro h s hs
      refine (Finset.mem_map' _).mp (h (π⁻¹ ⬝ s) ?_)
      have := hs.perm π⁻¹
      rwa [inv_perm_perm] at this
    · intro h s hs
      have := h (π ⬝ s) (hs.perm π)
      rwa [Finset.mem_perm] at this
  · rw [supp_eq_of_not_finitelySupported x hx, supp_eq_of_not_finitelySupported]
    · simp only [Finperm.perm_name_eq, Finset.notMem_empty]
    · contrapose! hx
      exact hx.of_perm

theorem Supports.map {α : Type*} [MulPerm 𝔸 α]
    {x : α} {s : Finset 𝔸} (h : Supports s x)
    {β : Type*} [MulPerm 𝔸 β] (f : α → β) (hf : Equivariant 𝔸 f) :
    Supports s (f x) := by
  intro π hπ
  rw [apply_perm_eq hf, h π hπ]

theorem Supports.of_map {α : Type*} [MulPerm 𝔸 α]
    {β : Type*} [MulPerm 𝔸 β]
    {x : α} {s : Finset 𝔸} {f : α → β} (h : Supports s (f x))
    (hf : Function.Injective f) (hf' : Equivariant 𝔸 f) :
    Supports s x := by
  intro π hπ
  have := h π hπ
  rw [apply_perm_eq hf'] at this
  exact hf this

theorem FinitelySupported.map {α : Type*} [MulPerm 𝔸 α]
    {x : α} (h : FinitelySupported 𝔸 x)
    {β : Type*} [MulPerm 𝔸 β] (f : α → β) (hf : Equivariant 𝔸 f) :
    FinitelySupported 𝔸 (f x) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, hs.map f hf⟩

theorem FinitelySupported.of_map {α : Type*} [MulPerm 𝔸 α]
    {β : Type*} [MulPerm 𝔸 β]
    {x : α} {f : α → β} (h : FinitelySupported 𝔸 (f x))
    (hf : Function.Injective f) (hf' : Equivariant 𝔸 f) :
    FinitelySupported 𝔸 x := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, hs.of_map hf hf'⟩

theorem supp_apply_subset {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β]
    (f : α → β) (hf : Equivariant 𝔸 f) (x : α) :
    supp 𝔸 (f x) ⊆ supp 𝔸 x := by
  intro a ha
  rw [Nominal.mem_supp_iff] at ha ⊢
  intro s hs
  exact ha s (hs.map f hf)

theorem Supports.apply {α β : Type*} [MulPerm 𝔸 α] [MulPerm 𝔸 β]
    {f : α → β} {s t : Finset 𝔸} (hf : Supports s f) {x : α} (hx : Supports t x) :
    Supports (s ∪ t) (f x) := by
  intro π hπ
  simp only [Finset.mem_union] at hπ
  have := hf π (λ a ha ↦ hπ a (Or.inl ha))
  simp only [funext_iff, Function.perm_def] at this
  have := this (π ⬝ x)
  rw [inv_perm_perm] at this
  rw [this, hx π (λ a ha ↦ hπ a (Or.inr ha))]

theorem supp_apply_subset' [Infinite 𝔸] {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β]
    (f : α → β) (hf : FinitelySupported 𝔸 f) (x : α) :
    supp 𝔸 (f x) ⊆ supp 𝔸 f ∪ supp 𝔸 x := by
  rw [Nominal.supp_subset_iff]
  apply Supports.apply
  exact supp_supports' f hf
  exact Nominal.supp_supports 𝔸 x

theorem supp_apply_eq_of_injective {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β]
    (f : α → β) (hf : Function.Injective f) (hf' : Equivariant 𝔸 f) (x : α) :
    supp 𝔸 (f x) = supp 𝔸 x := by
  apply subset_antisymm
  · exact supp_apply_subset f hf' x
  intro a ha
  rw [Nominal.mem_supp_iff] at ha ⊢
  intro s hs
  exact ha s (hs.of_map hf hf')

theorem finitelySupported_of_surjective {α β : Type*} [Nominal 𝔸 α] [MulPerm 𝔸 β]
    (f : α → β) (hf : Function.Surjective f) (hf' : Equivariant 𝔸 f) (y : β) :
    FinitelySupported 𝔸 y := by
  obtain ⟨x, rfl⟩ := hf y
  exact (Nominal.supported x).map f hf'

def nominal_of_surjective {α β : Type*} [Nominal 𝔸 α] [MulPerm 𝔸 β]
    (f : α → β) (hf : Function.Surjective f) (hf' : Equivariant 𝔸 f) :
    Nominal 𝔸 β where
  supported := finitelySupported_of_surjective f hf hf'

theorem equivariant_of_implies₂ {α β : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] {f : α → β → Prop}
    (h : ∀ π : Finperm 𝔸, ∀ x y, f x y → f (π ⬝ x) (π ⬝ y)) :
    Equivariant 𝔸 f := by
  simp only [Function.equivariant_iff, funext_iff, Function.perm_def, perm_prop, eq_iff_iff]
  intro π x y
  constructor
  · have := h π x (π⁻¹ ⬝ y)
    rwa [perm_inv_perm] at this
  · have := h π⁻¹ (π ⬝ x) y
    rwa [inv_perm_perm] at this

def id_equivariant {α : Sort*} [MulPerm 𝔸 α] : Equivariant 𝔸 (id : α → α) :=
  (Function.equivariant_iff id).mpr (λ _ _ ↦ rfl)

theorem Equivariant.comp {α β γ : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    {f : β → γ} {g : α → β}
    (hf : Equivariant 𝔸 f) (hg : Equivariant 𝔸 g) :
    Equivariant 𝔸 (f ∘ g) := by
  rw [Function.equivariant_iff]
  simp only [Function.comp_apply, apply_perm_eq hf, apply_perm_eq hg, implies_true]

theorem Equivariant.comp₂ {α β γ δ : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ] [MulPerm 𝔸 δ]
    {f : γ → δ} {g : α → β → γ}
    (hf : Equivariant 𝔸 f) (hg : Equivariant 𝔸 g) :
    Equivariant 𝔸 (λ x y ↦ f (g x y)) := by
  simp only [Function.equivariant_iff, funext_iff, Function.perm_def] at hf hg ⊢
  simp only [hf, hg, implies_true]

theorem FinitelySupported.comp {α β γ : Sort*} [MulPerm 𝔸 α] [MulPerm 𝔸 β] [MulPerm 𝔸 γ]
    {f : β → γ} {g : α → β}
    (hf : FinitelySupported 𝔸 f) (hg : FinitelySupported 𝔸 g) :
    FinitelySupported 𝔸 (f ∘ g) := by
  rw [Function.finitelySupported_iff] at hf hg ⊢
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  use s ∪ t
  intro π hπ x
  simp only [Function.comp_apply]
  rw [hs, ht]
  · intro a ha
    rw [hπ a (Finset.mem_union_right s ha)]
  · intro a ha
    rw [hπ a (Finset.mem_union_left t ha)]

theorem FinitelySupported.finite_or_finite [Infinite 𝔸]
    {p : 𝔸 → Prop} (hp : FinitelySupported 𝔸 p) :
    {x | p x}.Finite ∨ {x | ¬p x}.Finite := by
  obtain ⟨s, hs⟩ := hp
  simp only [Supports, funext_iff, Function.perm_def, perm_name_eq, perm_prop, eq_iff_iff] at hs
  have : ∀ a ∉ s, ∀ b ∉ s, p a ↔ p b := by
    intro a ha b hb
    have := hs (swap a b) ?_ b
    · rwa [swap_inv, swap_apply_right] at this
    · intro c hc
      rw [swap_apply_of_ne_of_ne] <;>
      · rintro rfl
        contradiction
  obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset s
  by_cases hb' : p b
  · right
    apply s.finite_toSet.subset
    intro c hc₁
    by_contra hc₂
    have := this b hb c hc₂
    exact hc₁ (this.mp hb')
  · left
    apply s.finite_toSet.subset
    intro c hc₁
    by_contra hc₂
    have := this b hb c hc₂
    exact hb' (this.mpr hc₁)
