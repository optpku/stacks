module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Open Restriction of Irreducible Closed Subsets

This module specializes Mathlib's open-embedding order isomorphism to the subtype of an open set.
-/

@[expose] public section

universe u

open Set TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace.IrreducibleCloseds

/-- The preimage of an irreducible closed subset along an open-subspace inclusion is irreducible
and closed when the subset meets the open subspace. -/
theorem restrictOpenCarrier_spec (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    IsIrreducible ((Subtype.val : U → X) ⁻¹' (Y : Set X)) ∧
      IsClosed ((Subtype.val : U → X) ⁻¹' (Y : Set X)) := sorry

/-- The irreducible closed subset of an open subspace obtained by intersecting an ambient
irreducible closed subset that meets the open. -/
def restrictOpen (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) : IrreducibleCloseds U :=
  ⟨Subtype.val ⁻¹' (Y : Set X),
    (restrictOpenCarrier_spec Y U hYU).1,
    (restrictOpenCarrier_spec Y U hYU).2⟩

/-- The carrier of an ambient irreducible closed subset restricted to an open subspace is its
set-theoretic preimage under the subtype inclusion. -/
@[simp]
theorem coe_restrictOpen (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    (Y.restrictOpen U hYU : Set U) = Subtype.val ⁻¹' (Y : Set X) := sorry

/-- Mapping an irreducible closed subset restricted to an open subspace back to the ambient space
recovers the original subset. -/
@[simp]
theorem map_restrictOpen_eq (Y : IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    IrreducibleCloseds.map (Subtype.val : U → X) continuous_subtype_val
      (Y.restrictOpen U hYU) = Y := sorry

end TopologicalSpace.IrreducibleCloseds

/-- An irreducible closed subset has the same codimension after restricting to an
open subspace that it meets. -/
@[stacks 02I4]
theorem coheight_eq_restrictOpen (Y : TopologicalSpace.IrreducibleCloseds X) (U : Opens X)
    (hYU : ((Y : Set X) ∩ U).Nonempty) :
    coheight Y = coheight (Y.restrictOpen U hYU) := sorry
