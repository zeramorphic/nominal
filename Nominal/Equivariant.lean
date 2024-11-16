import Nominal.Basic

variable {𝔸 : Type*} [DecidableEq 𝔸]

def Equivariant (𝔸 : Type*) [DecidableEq 𝔸]
    {α β : Type*} [MulAction (Finperm 𝔸) α] [MulAction (Finperm 𝔸) β]
    (f : α → β) : Prop :=
  ∀ π : Finperm 𝔸, ∀ x : α, π • f x = f (π • x)

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
