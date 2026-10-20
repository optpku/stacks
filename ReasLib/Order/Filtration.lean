module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lattice Representatives for Subquotient Filtrations

This file is independent of categories and modules.  It records the ambient-lattice
representatives of the stages of a filtration induced on a subquotient, together with the
separatedness and exhaustiveness conditions on those representatives.
-/

@[expose] public section

universe u v

namespace Order
namespace Filtration
namespace Subquotient

variable {I : Type u} {L : Type v}

/-- The ambient representative of the `i`-th stage of the filtration induced on the formal
subquotient `Y / X`: `(Y ⊓ F i) ⊔ X`.  The definition only needs lattice operations, so it
applies equally to subobjects, submodules, ideals, and other complete lattices. -/
@[stacks 012J "ambient representative of an induced subquotient filtration"]
def representative [Min L] [Max L] (F : I → L) (X Y : L) (i : I) : L :=
  (Y ⊓ F i) ⊔ X

section CompleteLattice

variable [CompleteLattice L]

/-- The ambient representatives of the induced filtration on `Y / X` are separated when their
infimum is `X`. -/
@[stacks 012J "separated subquotient-filtration criterion"]
def IsSeparated (F : I → L) (X Y : L) : Prop :=
  (⨅ i : I, representative F X Y i) = X

/-- The ambient representatives of the induced filtration on `Y / X` are exhaustive when their
supremum is `Y`. -/
@[stacks 012J "exhaustive subquotient-filtration criterion"]
def IsExhaustive (F : I → L) (X Y : L) : Prop :=
  (⨆ i : I, representative F X Y i) = Y

/-- The ambient representatives of the induced filtration on `Y / X` are both separated and
exhaustive.  When `X ≤ Y`, this is the presentation-free lattice criterion for the induced
filtration on that subquotient. -/
@[stacks 012J "separated and exhaustive subquotient-filtration criterion"]
def IsSeparatedExhaustive (F : I → L) (X Y : L) : Prop :=
  IsSeparated F X Y ∧ IsExhaustive F X Y

end CompleteLattice

end Subquotient
end Filtration
end Order
