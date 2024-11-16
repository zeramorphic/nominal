import Nominal.Equivariant

open Finperm

variable {𝔸 α β : Type*} [DecidableEq 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β]

def Fresh (𝔸 : Type*) [DecidableEq 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] (x : α) (y : β) : Prop :=
  Disjoint (supp 𝔸 x) (supp 𝔸 y)

notation:50 x " #[" 𝔸:50 "] " y:50 => Fresh 𝔸 x y

binder_predicate x " #["𝔸:term"] " y:term => `($x #[$𝔸] $y)

theorem fresh_def (x : α) (y : β) :
    x #[𝔸] y ↔ Disjoint (supp 𝔸 x) (supp 𝔸 y) :=
  Iff.rfl

theorem name_fresh_iff [Infinite 𝔸] (a : 𝔸) (x : α) :
    a #[𝔸] x ↔ a ∉ supp 𝔸 x := by
  rw [fresh_def, Nominal.name_supp_eq, Finset.disjoint_singleton_left]

@[simp]
theorem false_of_fresh_of_mem_supp [Infinite 𝔸] (a : 𝔸) (x : α) :
    a #[𝔸] x → a ∈ supp 𝔸 x → False := by
  rw [name_fresh_iff]
  exact id

theorem exists_fresh [Infinite 𝔸] (x : α) :
    ∃ a : 𝔸, a #[𝔸] x := by
  simp only [name_fresh_iff]
  exact Infinite.exists_not_mem_finset (supp 𝔸 x)

theorem swap_smul_eq_of_fresh [Infinite 𝔸] (a b : 𝔸) (x : α) (ha : a #[𝔸] x) (hb : b #[𝔸] x) :
    swap a b • x = x := by
  apply Nominal.supp_supports 𝔸 x (swap a b)
  intro c hc
  rw [smul_name_eq, swap_apply_of_ne_of_ne]
  · rintro rfl
    exact false_of_fresh_of_mem_supp c x ha hc
  · rintro rfl
    exact false_of_fresh_of_mem_supp c x hb hc

theorem EquivariantRel.rename_of_fresh [Infinite 𝔸]
    {p : 𝔸 → α → Prop} (h : EquivariantRel 𝔸 p) (a b : 𝔸) (x : α)
    (ha : a #[𝔸] x) (hb : b #[𝔸] x) :
    p a x ↔ p b x := by
  have := h (swap a b) b x
  convert this using 2
  · simp only [smul_name_eq, swap_apply_right]
  · rw [swap_smul_eq_of_fresh a b x ha hb]
