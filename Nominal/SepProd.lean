import Nominal.Instances
import Nominal.Rel

open Rel

/-- The *separated product* of `α` and `β` with respect to the name set `𝔸`. -/
@[ext]
structure SepProd (𝔸 : Type*) [DecidableEq 𝔸] (α β : Type*) [MulPerm 𝔸 α] [MulPerm 𝔸 β] where
  fst : α
  snd : β
  sep : fst #[𝔸] snd

@[inherit_doc] notation:35 α " ∗["𝔸"] " β:34 => SepProd 𝔸 α β

namespace SepProd

variable {𝔸 : Type*} [DecidableEq 𝔸] {α β γ δ : Type*}

instance [MulPerm 𝔸 α] [MulPerm 𝔸 β] : HasPerm 𝔸 (α ∗[𝔸] β) where
  perm π x := ⟨π ⬝ x.fst, π ⬝ x.snd, x.sep.perm π⟩

@[simp]
theorem perm_fst [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : α ∗[𝔸] β) (π : Finperm 𝔸) :
    (π ⬝ x).fst = π ⬝ x.fst :=
  rfl

@[simp]
theorem perm_snd [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : α ∗[𝔸] β) (π : Finperm 𝔸) :
    (π ⬝ x).snd = π ⬝ x.snd :=
  rfl

instance [MulPerm 𝔸 α] [MulPerm 𝔸 β] : MulPerm 𝔸 (α ∗[𝔸] β) where
  one_perm := by intros; ext <;> simp only [perm_fst, perm_snd, one_perm]
  mul_perm := by intros; ext <;> simp only [perm_fst, perm_snd, mul_perm]

def toProd [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : α ∗[𝔸] β) : α × β :=
  (x.fst, x.snd)

theorem toProd_injective [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    Function.Injective (toProd : α ∗[𝔸] β → α × β) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  cases h
  rfl

theorem toProd_equivariant [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    Equivariant 𝔸 (toProd : α ∗[𝔸] β → α × β) := by
  intro π
  ext x : 1
  simp only [Function.perm_def, toProd, perm_fst, perm_snd, Prod.perm_mk, perm_inv_perm]

instance [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] : Nominal 𝔸 (α ∗[𝔸] β) where
  supported x := by
    use supp 𝔸 x.fst ∪ supp 𝔸 x.snd
    intro π hπ
    simp only [Finset.mem_union] at hπ
    ext
    · exact Nominal.supp_supports 𝔸 x.fst π (λ a ha ↦ hπ a (Or.inl ha))
    · exact Nominal.supp_supports 𝔸 x.snd π (λ a ha ↦ hπ a (Or.inr ha))

@[simp]
theorem supp_eq [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] (x : α ∗[𝔸] β) :
    supp 𝔸 x = supp 𝔸 x.fst ∪ supp 𝔸 x.snd := by
  rw [← supp_apply_eq_of_injective toProd toProd_injective toProd_equivariant,
    Prod.supp_mk]
  rfl

/-!
# (Bi)functoriality
-/

def bimap [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ] [Nominal 𝔸 δ]
    (f : α → γ) (g : β → δ) (hf : Equivariant 𝔸 f) (hg : Equivariant 𝔸 g)
    (x : α ∗[𝔸] β) : γ ∗[𝔸] δ :=
  ⟨f x.fst, g x.snd, by
    have := x.sep
    rw [fresh_def, Finset.disjoint_iff_ne] at this ⊢
    intro a ha b hb
    exact this a (supp_apply_subset f hf x.fst ha) b (supp_apply_subset g hg x.snd hb)⟩

@[simp]
theorem bimap_fst [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ] [Nominal 𝔸 δ]
    {f : α → γ} {g : β → δ} {hf : Equivariant 𝔸 f} {hg : Equivariant 𝔸 g}
    (x : α ∗[𝔸] β) :
    (bimap f g hf hg x).fst = f x.fst :=
  rfl

@[simp]
theorem bimap_snd [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ] [Nominal 𝔸 δ]
    {f : α → γ} {g : β → δ} {hf : Equivariant 𝔸 f} {hg : Equivariant 𝔸 g}
    (x : α ∗[𝔸] β) :
    (bimap f g hf hg x).snd = g x.snd :=
  rfl

def first [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : α → γ) (hf : Equivariant 𝔸 f) : α ∗[𝔸] β → γ ∗[𝔸] β :=
  bimap f id hf id_equivariant

@[simp]
theorem first_fst [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    {f : α → γ} {hf : Equivariant 𝔸 f} (x : α ∗[𝔸] β) :
    (first f hf x).fst = f x.fst :=
  rfl

@[simp]
theorem first_snd [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    {f : α → γ} {hf : Equivariant 𝔸 f} (x : α ∗[𝔸] β) :
    (first f hf x).snd = x.snd :=
  rfl

def second [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : β → γ) (hf : Equivariant 𝔸 f) : α ∗[𝔸] β → α ∗[𝔸] γ :=
  bimap id f id_equivariant hf

@[simp]
theorem second_fst [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    {f : β → γ} {hf : Equivariant 𝔸 f} (x : α ∗[𝔸] β) :
    (second f hf x).fst = x.fst :=
  rfl

@[simp]
theorem second_snd [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    {f : β → γ} {hf : Equivariant 𝔸 f} (x : α ∗[𝔸] β) :
    (second f hf x).snd = f x.snd :=
  rfl

/-!
# Monoid structure
-/

/-- The monoidal symmetry. -/
def symm (α β : Type*) [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    α ∗[𝔸] β ≃ β ∗[𝔸] α where
  toFun x := ⟨x.snd, x.fst, x.sep.comm⟩
  invFun x := ⟨x.snd, x.fst, x.sep.comm⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem symm_fst [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : α ∗[𝔸] β) :
    (symm α β x).fst = x.snd :=
  rfl

@[simp]
theorem symm_snd [MulPerm 𝔸 α] [MulPerm 𝔸 β] (x : α ∗[𝔸] β) :
    (symm α β x).snd = x.fst :=
  rfl

theorem symm_equivariant [MulPerm 𝔸 α] [MulPerm 𝔸 β] :
    Equivariant 𝔸 (symm α β : α ∗[𝔸] β → β ∗[𝔸] α) := by
  intro π
  ext x
  · simp only [Function.perm_def, perm_fst, symm_fst, perm_snd, perm_inv_perm]
  · simp only [Function.perm_def, perm_snd, symm_snd, perm_fst, perm_inv_perm]

def leftDiscrete (α β : Type*) [MulPerm 𝔸 α] [MulPerm 𝔸 β] [IsDiscrete 𝔸 α] :
    α ∗[𝔸] β ≃ α × β where
  toFun := toProd
  invFun x := ⟨x.fst, x.snd, by
    rw [fresh_def, IsDiscrete.supp_eq]
    exact Finset.disjoint_empty_left _⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem leftDiscrete_apply_eq [MulPerm 𝔸 α] [MulPerm 𝔸 β] [IsDiscrete 𝔸 α]
    (x : α ∗[𝔸] β) :
    leftDiscrete α β x = toProd x :=
  rfl

def rightDiscrete (α β : Type*) [MulPerm 𝔸 α] [MulPerm 𝔸 β] [IsDiscrete 𝔸 β] :
    α ∗[𝔸] β ≃ α × β :=
  (symm α β).trans ((leftDiscrete β α).trans (Equiv.prodComm β α))

@[simp]
theorem rightDiscrete_apply_eq [MulPerm 𝔸 α] [MulPerm 𝔸 β] [IsDiscrete 𝔸 β]
    (x : α ∗[𝔸] β) :
    rightDiscrete α β x = toProd x :=
  rfl

/-- The monoidal left unitor. -/
def leftUnitor (α : Type*) [MulPerm 𝔸 α] :
    Unit ∗[𝔸] α ≃ α :=
  (leftDiscrete Unit α).trans (Equiv.punitProd α)

@[simp]
theorem leftUnitor_apply_eq [MulPerm 𝔸 α] (x : Unit ∗[𝔸] α) :
    leftUnitor α x = x.snd :=
  rfl

@[simp]
theorem leftUnitor_symm_apply_snd_eq [MulPerm 𝔸 α] (x : α) :
    ((leftUnitor α : Unit ∗[𝔸] α ≃ α).symm x).snd = x :=
  rfl

/-- The monoidal right unitor. -/
def rightUnitor (α : Type*) [MulPerm 𝔸 α] :
    α ∗[𝔸] Unit ≃ α :=
  (rightDiscrete α Unit).trans (Equiv.prodPUnit α)

@[simp]
theorem rightUnitor_apply_eq [MulPerm 𝔸 α] (x : α ∗[𝔸] Unit) :
    rightUnitor α x = x.fst :=
  rfl

@[simp]
theorem rightUnitor_symm_apply_snd_eq [MulPerm 𝔸 α] (x : α) :
    ((rightUnitor α : α ∗[𝔸] Unit ≃ α).symm x).fst = x :=
  rfl

def assoc' [Infinite 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (x : (α ∗[𝔸] β) ∗[𝔸] γ) : α ∗[𝔸] β ∗[𝔸] γ where
  fst := x.fst.fst
  snd := ⟨x.fst.snd, x.snd, by
    have := x.sep
    rw [fresh_def] at this ⊢
    simp only [supp_eq, Finset.disjoint_union_left] at this
    aesop⟩
  sep := by
    have := x.sep
    rw [fresh_def] at this ⊢
    rw [supp_eq, Finset.disjoint_union_left] at this
    rw [supp_eq, Finset.disjoint_union_right]
    exact ⟨x.fst.sep, this.1⟩

/-- The monoidal associator. -/
def assoc [Infinite 𝔸] (α β γ : Type*) [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ] :
    (α ∗[𝔸] β) ∗[𝔸] γ ≃ α ∗[𝔸] β ∗[𝔸] γ where
  toFun := assoc'
  invFun := first (symm β α) symm_equivariant ∘ symm γ (β ∗[𝔸] α) ∘
    assoc' ∘ first (symm β γ) symm_equivariant ∘ symm α (β ∗[𝔸] γ)
  left_inv _ := rfl
  right_inv _ := rfl

end SepProd

/-!
# Right adjoint

Here, we define *separating implication*, the right adjoint to the functor `- ∗[𝔸] α`.
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

variable {𝔸 : Type*} [DecidableEq 𝔸] {α β γ δ : Type*}

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
    simp only [supp_perm_eq, Finperm.perm_name_eq, Finset.mem_sdiff, Finset.mem_perm,
      _root_.inv_inv, Finperm.apply_inv_self]
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
  rw [or_iff_not_imp_left, not_isEmpty_iff, Nonempty.forall]
  intro y
  apply subset_antisymm
  · exact supp_minimal _ _ (supports_unit x)
  intro a ha
  rw [mem_supp_iff' _ ⟨_, supports_unit x⟩]
  intro s hs
  by_contra ha'
  -- TODO: We need a way to make a new `y` that is fresh for `x`.
  sorry

/-- The unit of the adjunction between separated product and separating implication. -/
def unit [Infinite 𝔸] [MulPerm 𝔸 α] [Nominal 𝔸 β] (x : β) : α -∗[𝔸] β ∗[𝔸] α where
  rel y z := z.fst = x ∧ z.snd = y
  rel_fs := ⟨supp 𝔸 x, supports_unit x⟩
  rel_coinjective := by constructor; aesop
  mem_dom_iff := sorry
  mem_supp_iff := sorry

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

end SepImp
