import Nominal.Equivariant

variable {𝔸 α β : Type*} [DecidableEq 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β]

def Fresh (x : α) (y : β) : Prop :=
  Disjoint (supp 𝔸 x) (supp 𝔸 y)

infix:50 " # " => Fresh
