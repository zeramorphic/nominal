import Nominal.Equivariant

open Finperm

variable {𝔸 α β : Type*} [DecidableEq 𝔸]

def Fresh (𝔸 : Type*) [DecidableEq 𝔸] [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : α) (y : β) : Prop :=
  Disjoint (supp 𝔸 x) (supp 𝔸 y)

notation:50 x " #[" 𝔸:50 "] " y:50 => Fresh 𝔸 x y

binder_predicate x " #["𝔸:term"] " y:term => `($x #[$𝔸] $y)

theorem fresh_def [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : α) (y : β) :
    x #[𝔸] y ↔ Disjoint (supp 𝔸 x) (supp 𝔸 y) :=
  Iff.rfl

theorem name_fresh_iff [Infinite 𝔸] [MulPerm 𝔸 α] (a : 𝔸) (x : α) :
    a #[𝔸] x ↔ a ∉ supp 𝔸 x := by
  rw [fresh_def, Nominal.name_supp_eq, Finset.disjoint_singleton_left]

@[simp]
theorem false_of_fresh_of_mem_supp [Infinite 𝔸] [MulPerm 𝔸 α] (a : 𝔸) (x : α) :
    a #[𝔸] x → a ∈ supp 𝔸 x → False := by
  rw [name_fresh_iff]
  exact id

@[simp]
theorem name_fresh_name_iff [Infinite 𝔸] (a b : 𝔸) :
    a #[𝔸] b ↔ a ≠ b := by
  simp only [name_fresh_iff, Nominal.name_supp_eq, Finset.mem_singleton, ne_eq]

theorem exists_fresh [Infinite 𝔸] [MulPerm 𝔸 α] (x : α) :
    ∃ a : 𝔸, a #[𝔸] x := by
  simp only [name_fresh_iff]
  exact Infinite.exists_not_mem_finset (supp 𝔸 x)

theorem swap_perm_eq_of_fresh [Infinite 𝔸] [Nominal 𝔸 α]
    (a b : 𝔸) (x : α) (ha : a #[𝔸] x) (hb : b #[𝔸] x) :
    swap a b ⬝ x = x := by
  apply Nominal.supp_supports 𝔸 x (swap a b)
  intro c hc
  rw [swap_apply_of_ne_of_ne]
  · rintro rfl
    exact false_of_fresh_of_mem_supp c x ha hc
  · rintro rfl
    exact false_of_fresh_of_mem_supp c x hb hc

theorem fresh_iff_forall_swap_perm_eq [Infinite 𝔸] [Nominal 𝔸 α] (a : 𝔸) (x : α) :
    a #[𝔸] x ↔ ∀ b #[𝔸] x, swap a b ⬝ x = x := by
  constructor
  · intro ha b hb
    rw [swap_perm_eq_of_fresh a b x ha hb]
  intro h
  rw [name_fresh_iff, Nominal.mem_supp_iff_names_infinite, Set.not_infinite]
  apply (supp 𝔸 x).finite_toSet.subset
  intro b hb
  by_contra hb'
  simp only [name_fresh_iff] at h
  exact hb (h b hb')

theorem fresh_iff_exists_swap_perm_eq [Infinite 𝔸] [Nominal 𝔸 α] (a : 𝔸) (x : α) :
    a #[𝔸] x ↔ ∃ b #[𝔸] x, swap a b ⬝ x = x := by
  constructor
  · rw [fresh_iff_forall_swap_perm_eq]
    intro h
    obtain ⟨b, hb⟩ := exists_fresh (𝔸 := 𝔸) x
    exact ⟨b, hb, h b hb⟩
  · rintro ⟨b, hb₁, hb₂⟩
    have := congr_arg (b ∈ supp 𝔸 ·) hb₂
    simp only [Nominal.supp_perm_eq, Finset.mem_perm_iff, swap_inv, perm_name_eq, swap_apply_right,
      eq_iff_iff] at this
    rw [name_fresh_iff] at hb₁ ⊢
    exact hb₁ ∘ this.mp

theorem Fresh.perm [Nominal 𝔸 α] [Nominal 𝔸 β] {x : α} {y : β} (h : x #[𝔸] y) (π : Finperm 𝔸) :
    (π ⬝ x) #[𝔸] (π ⬝ y) := by
  simp only [fresh_def, Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_not_mem,
    Finset.mem_inter, not_and, Nominal.supp_perm_eq, Finset.mem_perm_iff, perm_name_eq] at h ⊢
  intro a ha₁ ha₂
  exact h _ ha₁ ha₂

theorem Equivariant.rename_of_fresh [Infinite 𝔸] [Nominal 𝔸 α]
    {p : 𝔸 → α → Prop} (h : Equivariant 𝔸 p) (a b : 𝔸) (x : α)
    (ha : a #[𝔸] x) (hb : b #[𝔸] x) :
    p a x ↔ p b x := by
  have := apply₂_perm_eq h (swap a b) b x
  simp only [perm_prop, perm_name_eq, swap_apply_right, eq_iff_iff] at this
  rw [this, swap_perm_eq_of_fresh a b x ha hb]
