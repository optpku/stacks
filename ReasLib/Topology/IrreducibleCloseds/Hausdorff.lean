module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Irreducible Closed Subsets of Hausdorff Spaces

The Hausdorff specialization of the canonical irreducibility API.
-/

@[expose] public section

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- Every irreducible closed subset of a Hausdorff space is a singleton. -/
@[stacks 004Y "irreducible closed subsets of Hausdorff spaces are singletons"]
theorem IrreducibleCloseds.exists_eq_singleton [T2Space X] (Z : IrreducibleCloseds X) :
    ∃ x : X, Z = {x} := by
  obtain ⟨x, hx⟩ := isIrreducible_iff_singleton.mp Z.isIrreducible
  exact ⟨x, IrreducibleCloseds.ext hx⟩
