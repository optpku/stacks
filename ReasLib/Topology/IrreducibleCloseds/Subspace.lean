/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Restriction of Irreducible Closed Subsets

This module provides restriction of an ambient irreducible closed subset to an arbitrary containing
subspace.
-/

@[expose] public section

universe u

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type u} [TopologicalSpace X]

/-- The preimage of an irreducible closed subset along a containing-subspace inclusion is
irreducible and closed. -/
theorem restrictCarrier_spec (T : IrreducibleCloseds X) (S : Set X)
    (hTS : (T : Set X) ⊆ S) :
    IsIrreducible ((Subtype.val : S → X) ⁻¹' (T : Set X)) ∧
      IsClosed ((Subtype.val : S → X) ⁻¹' (T : Set X)) := sorry

/-- Restrict an ambient irreducible closed subset to any subspace containing it. -/
noncomputable def restrict (T : IrreducibleCloseds X) (S : Set X)
    (hTS : (T : Set X) ⊆ S) : IrreducibleCloseds S :=
  ⟨Subtype.val ⁻¹' (T : Set X),
    (restrictCarrier_spec T S hTS).1,
    (restrictCarrier_spec T S hTS).2⟩

/-- The carrier of an irreducible closed subset restricted to a containing subspace is its
set-theoretic preimage under the subtype inclusion. -/
@[simp]
theorem coe_restrict (T : IrreducibleCloseds X) (S : Set X)
    (hTS : (T : Set X) ⊆ S) :
    (T.restrict S hTS : Set S) = Subtype.val ⁻¹' (T : Set X) := sorry

/-- Mapping a restricted irreducible closed subset back to the ambient space recovers the
original subset. -/
@[simp]
theorem map_restrict_eq (T : IrreducibleCloseds X) (S : Set X)
    (hTS : (T : Set X) ⊆ S) :
    IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val
      (T.restrict S hTS) = T := sorry

/-- Restriction of irreducible closed subsets to a common containing subspace is monotone. -/
theorem restrict_mono {T T' : IrreducibleCloseds X} (S : Set X)
    (hTS : (T : Set X) ⊆ S) (hT'S : (T' : Set X) ⊆ S) (hTT' : T ≤ T') :
    T.restrict S hTS ≤ T'.restrict S hT'S := sorry

end TopologicalSpace.IrreducibleCloseds
