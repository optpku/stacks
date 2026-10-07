module

public import ReasLib.Topology.ConnectedComponents.ClosedPoints
public import ReasLib.Topology.OpenCover.DisjointClopen

/-!
# Disjoint clopen refinements in spectral spaces

Closed-point criteria for finite disjoint clopen refinements of open covers.
-/

@[expose] public section

open Set Topology

universe u

namespace SpectralSpace

/-- Every open cover of a spectral space admits a finite pairwise disjoint
clopen refinement exactly when its closed points map bijectively to its
connected components. -/
theorem hasFiniteDisjointClopenCoverRefinement_iff_bijective_fromClosedPoints
    {X : Type u} [TopologicalSpace X] [SpectralSpace X] :
    HasFiniteDisjointClopenCoverRefinement X ↔
      Function.Bijective
        (ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X) := sorry

/-- If the closed points of a spectral space form a closed subset and every
point specializes to a unique closed point, then the canonical map from closed
points to connected components is bijective. -/
theorem bijective_fromClosedPoints_of_uniqueClosedPointSpecialization
    {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    (h_closed : IsClosed (closedPoints X))
    (h_unique : HasUniqueClosedPointSpecialization X) :
    Function.Bijective
      (ConnectedComponents.fromClosedPoints : closedPoints X → ConnectedComponents X) := sorry

end SpectralSpace
