module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import Mathlib.Topology.Separation.Basic

/-!
# Points of the spectrum of a field

The algebraic space represented by the spectrum of a field has a canonical unique point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

/-- The canonical point of the algebraic space represented by the spectrum of a field. -/
def specFieldPoint (k : Type u) [Field k] :
    Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :=
  ofOver.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (default : Spec (CommRingCat.of k))

/-- The algebraic space represented by the spectrum of a field has a unique point. -/
instance instUnique_specField (k : Type u) [Field k] :
    Unique (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
  @Equiv.unique _ _ (inferInstanceAs (Unique (PrimeSpectrum k)))
    (ofOver.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm

end AlgebraicGeometry.AlgebraicSpace.Points

