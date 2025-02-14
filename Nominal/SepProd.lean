import Nominal.Instances

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

def map [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ] [Nominal 𝔸 δ]
    (f : α → γ) (g : β → δ) (hf : Equivariant 𝔸 f) (hg : Equivariant 𝔸 g)
    (x : α ∗[𝔸] β) : γ ∗[𝔸] δ :=
  ⟨f x.fst, g x.snd, by
    have := x.sep
    rw [fresh_def, Finset.disjoint_iff_ne] at this ⊢
    intro a ha b hb
    exact this a (supp_apply_subset f hf x.fst ha) b (supp_apply_subset g hg x.snd hb)⟩

@[simp]
theorem map_fst [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ] [Nominal 𝔸 δ]
    {f : α → γ} {g : β → δ} {hf : Equivariant 𝔸 f} {hg : Equivariant 𝔸 g}
    (x : α ∗[𝔸] β) :
    (map f g hf hg x).fst = f x.fst :=
  rfl

@[simp]
theorem map_snd [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ] [Nominal 𝔸 δ]
    {f : α → γ} {g : β → δ} {hf : Equivariant 𝔸 f} {hg : Equivariant 𝔸 g}
    (x : α ∗[𝔸] β) :
    (map f g hf hg x).snd = g x.snd :=
  rfl

def first [Nominal 𝔸 α] [Nominal 𝔸 β] [Nominal 𝔸 γ]
    (f : α → γ) (hf : Equivariant 𝔸 f) : α ∗[𝔸] β → γ ∗[𝔸] β :=
  map f id hf id_equivariant

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
  map id f id_equivariant hf

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
