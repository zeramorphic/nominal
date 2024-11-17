import Nominal.Basic

open Finperm

variable {𝔸 : Type*} [DecidableEq 𝔸]

def Equivariant (𝔸 : Type*) [DecidableEq 𝔸]
    {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (f : α → β) : Prop :=
  ∀ π : Finperm 𝔸, ∀ x, π • f x = f (π • x)

def EquivariantPred (𝔸 : Type*) [DecidableEq 𝔸] {α : Type*} [MulAction (Finperm 𝔸) α]
    (p : α → Prop) : Prop :=
  ∀ π : Finperm 𝔸, ∀ x, p (π • x) ↔ p x

def EquivariantRel (𝔸 : Type*) [DecidableEq 𝔸]
    {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (p : α → β → Prop) : Prop :=
  ∀ π : Finperm 𝔸, ∀ x y, p (π • x) (π • y) ↔ p x y

-- Note: FinitelySupported is already defined.

def FinitelySupportedPred (𝔸 : Type*) [DecidableEq 𝔸] {α : Type*} [MulAction (Finperm 𝔸) α]
    (p : α → Prop) : Prop :=
  ∃ s : Finset 𝔸, ∀ π : Finperm 𝔸, (∀ a ∈ s, π • a = a) → ∀ x, p (π • x) ↔ p x

def FinitelySupportedRel (𝔸 : Type*) [DecidableEq 𝔸]
    {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (p : α → β → Prop) : Prop :=
  ∃ s : Finset 𝔸, ∀ π : Finperm 𝔸, (∀ a ∈ s, π • a = a) → ∀ x y, p (π • x) (π • y) ↔ p x y

theorem supp_equivariant [Infinite 𝔸] {α : Type*} [MulAction (Finperm 𝔸) α] :
    Equivariant 𝔸 (supp 𝔸 : α → Finset 𝔸) := by
  intro π x
  ext a
  rw [Finset.mem_smul_iff]
  by_cases hx : FinitelySupported 𝔸 x
  · rw [mem_supp_iff' x hx, mem_supp_iff' (π • x) (hx.smul π)]
    constructor
    · intro h s hs
      refine (Finset.mem_map' _).mp (h (π⁻¹ • s) ?_)
      have := hs.smul' π⁻¹
      rwa [inv_smul_smul] at this
    · intro h s hs
      have := h (π • s) (hs.smul' π)
      rwa [Finset.mem_smul_iff] at this
  · rw [supp_eq_of_not_finitelySupported x hx, supp_eq_of_not_finitelySupported]
    · simp only [Finperm.smul_name_eq, Finset.not_mem_empty]
    · contrapose! hx
      exact hx.of_smul

theorem MulAction.Supports.map {α : Type*} [MulAction (Finperm 𝔸) α]
    {x : α} {s : Set 𝔸} (h : Supports (Finperm 𝔸) s x)
    {β : Type*} [MulAction (Finperm 𝔸) β] (f : α → β) (hf : Equivariant 𝔸 f) :
    Supports (Finperm 𝔸) s (f x) := by
  intro π hπ
  rw [hf, h π hπ]

theorem MulAction.Supports.of_map {α : Type*} [MulAction (Finperm 𝔸) α]
    {β : Type*} [MulAction (Finperm 𝔸) β]
    {x : α} {s : Set 𝔸} {f : α → β} (h : Supports (Finperm 𝔸) s (f x))
    (hf : Function.Injective f) (hf' : Equivariant 𝔸 f) :
    Supports (Finperm 𝔸) s x := by
  intro π hπ
  have := h π hπ
  rw [hf'] at this
  exact hf this

theorem FinitelySupported.map {α : Type*} [MulAction (Finperm 𝔸) α]
    {x : α} (h : FinitelySupported 𝔸 x)
    {β : Type*} [MulAction (Finperm 𝔸) β] (f : α → β) (hf : Equivariant 𝔸 f) :
    FinitelySupported 𝔸 (f x) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, hs.map f hf⟩

theorem FinitelySupported.of_map {α : Type*} [MulAction (Finperm 𝔸) α]
    {β : Type*} [MulAction (Finperm 𝔸) β]
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

theorem supp_apply_eq_of_injective {α β : Type*} [Nominal 𝔸 α] [Nominal 𝔸 β]
    (f : α → β) (hf : Function.Injective f) (hf' : Equivariant 𝔸 f) (x : α) :
    supp 𝔸 (f x) = supp 𝔸 x := by
  apply subset_antisymm
  · exact supp_apply_subset f hf' x
  intro a ha
  rw [Nominal.mem_supp_iff] at ha ⊢
  intro s hs
  exact ha s (hs.of_map hf hf')

theorem finitelySupported_of_surjective {α β : Type*} [Nominal 𝔸 α] [MulAction (Finperm 𝔸) β]
    (f : α → β) (hf : Function.Surjective f) (hf' : Equivariant 𝔸 f) (y : β) :
    FinitelySupported 𝔸 y := by
  obtain ⟨x, rfl⟩ := hf y
  exact (Nominal.supported x).map f hf'

def nominal_of_surjective {α β : Type*} [Nominal 𝔸 α] [MulAction (Finperm 𝔸) β]
    (f : α → β) (hf : Function.Surjective f) (hf' : Equivariant 𝔸 f) :
    Nominal 𝔸 β where
  supported := finitelySupported_of_surjective f hf hf'

theorem EquivariantRel.not {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    {p : α → β → Prop} (h : EquivariantRel 𝔸 p) : EquivariantRel 𝔸 (λ x y ↦ ¬p x y) := by
  intro π x y
  dsimp only
  rw [h π x y]

theorem FinitelySupportedPred.not {α : Type*} [MulAction (Finperm 𝔸) α] {p : α → Prop}
    (hp : FinitelySupportedPred 𝔸 p) :
    FinitelySupportedPred 𝔸 (λ x ↦ ¬p x) := by
  obtain ⟨s, hs⟩ := hp
  use s
  intro π hπ x
  dsimp only
  rw [hs π hπ x]

theorem FinitelySupportedPred.finite_or_finite [Infinite 𝔸]
    {p : 𝔸 → Prop} (hp : FinitelySupportedPred 𝔸 p) :
    {x | p x}.Finite ∨ {x | ¬p x}.Finite := by
  obtain ⟨s, hs⟩ := hp
  have : ∀ a ∉ s, ∀ b ∉ s, p a ↔ p b := by
    intro a ha b hb
    have := hs (swap a b) ?_ b
    · rwa [smul_name_eq, swap_apply_right] at this
    · intro c hc
      rw [smul_name_eq, swap_apply_of_ne_of_ne] <;>
      · rintro rfl
        contradiction
  obtain ⟨b, hb⟩ := Infinite.exists_not_mem_finset s
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
