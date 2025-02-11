import Nominal.Instances
import Nominal.Quantifier

open Finperm

variable {𝔸 α β : Type*} [DecidableEq 𝔸]

structure Abstract' (𝔸 α β : Type*) where
  param : α
  val : β

namespace Abstract'

variable [MulPerm 𝔸 α] [MulPerm 𝔸 β]

instance : HasPerm 𝔸 (Abstract' 𝔸 α β) where
  perm π x := ⟨π ⬝ x.param, π ⬝ x.val⟩

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
  ∃ π : Finperm 𝔸, π ⬝ x = y ∧ π #[𝔸] (supp 𝔸 x.1 \ supp 𝔸 x.2)

theorem perm_supp_diff_eq [Infinite 𝔸] (π : Finperm 𝔸) (x : Abstract' 𝔸 α β) :
    π ⬝ (supp 𝔸 x.1 \ supp 𝔸 x.2) = supp 𝔸 (π ⬝ x).1 \ supp 𝔸 (π ⬝ x).2 := by
  ext a
  rw [Finset.perm_def]
  simp only [perm_def, supp_perm_eq, Finset.mem_sdiff, Finset.mem_perm_iff, perm_name_eq,
    Finset.mem_map, Function.Embedding.coeFn_mk]
  aesop

theorem perm_supp_diff_eq' [Infinite 𝔸] {π : Finperm 𝔸} {x : Abstract' 𝔸 α β}
    (h : π #[𝔸] (supp 𝔸 x.1 \ supp 𝔸 x.2)) :
    supp 𝔸 (π ⬝ x).1 \ supp 𝔸 (π ⬝ x).2 = supp 𝔸 x.1 \ supp 𝔸 x.2 := by
  rw [← perm_supp_diff_eq, perm_eq_of_fresh h]

theorem rel_refl [Infinite 𝔸] (x : Abstract' 𝔸 α β) :
    Rel x x := by
  use 1
  simp only [one_perm, fresh_iff, coe_one, id_eq, implies_true, and_self]

theorem rel_symm {x y : Abstract' 𝔸 α β} (h : Rel x y) :
    Rel y x := by
  sorry

theorem rel_trans {x y z : Abstract' 𝔸 α β} (h₁ : Rel x y) (h₂ : Rel y z) :
    Rel x z := by
  sorry

theorem rel_equivalence [Infinite 𝔸] :
    Equivalence (Rel : Abstract' 𝔸 α β → Abstract' 𝔸 α β → Prop) :=
  ⟨rel_refl, rel_symm, rel_trans⟩

instance [Infinite 𝔸] : Setoid (Abstract' 𝔸 α β) where
  r := Rel (𝔸 := 𝔸)
  iseqv := rel_equivalence

end Abstract'
