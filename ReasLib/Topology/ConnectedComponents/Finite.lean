/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.NoetherianSpace
public import ReasLib.Topology.ConnectedComponents.Set

/-!
# Finiteness of connected-component quotients

This leaf records finiteness criteria for the connected-component quotient.  It also records that
finite irreducible-component families make the subsets represented by connected components
clopen.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A compact space whose connected components are open has finitely many connected components. -/
theorem finite_connectedComponents_of_compactSpace_of_isOpen_connectedComponent
    [CompactSpace X]
    (hopen : ∀ x : X, IsOpen (connectedComponent x)) :
    Finite (ConnectedComponents X) := by
  -- Local instance justification (proof-local temporary data): quotient compactness is needed
  -- only to apply the compact-discrete finiteness criterion.
  letI : CompactSpace (ConnectedComponents X) :=
    Function.Surjective.compactSpace ConnectedComponents.continuous_coe
      ConnectedComponents.surjective_coe
  -- Local instance justification (proof-local temporary data): component openness supplies
  -- quotient discreteness only for this compact-discrete finiteness proof.
  letI : DiscreteTopology (ConnectedComponents X) :=
    ConnectedComponents.discreteTopology_iff.mpr hopen
  exact finite_of_compact_of_discrete

/-- A space with finitely many irreducible components has finitely many connected components. -/
theorem finite_connectedComponents_of_finite_irreducibleComponents
    [Finite (irreducibleComponents X)] :
    Finite (ConnectedComponents X) := sorry

namespace ConnectedComponents

/-- In a space with finitely many irreducible components, every connected component is clopen. -/
theorem isClopen_set_of_finite_irreducibleComponents
    [Finite (irreducibleComponents X)] (C : ConnectedComponents X) :
    IsClopen C.set := sorry

end ConnectedComponents
