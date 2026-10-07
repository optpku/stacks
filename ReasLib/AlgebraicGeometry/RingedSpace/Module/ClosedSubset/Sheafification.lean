module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset

@[expose] public section

/-!
# Sheafification on closed subspaces

This module records the sheafification compatibility needed to compare intrinsic closed
ringed-subspace modules with the restricted structure-sheaf presentation.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset

/-- Forgetting commutativity preserves sheafification on the topology of a closed subspace. -/
noncomputable instance preservesSheafificationForgetCommRing (X : RingedSpace.{u})
    (Z : Closeds X) :
    (Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u}) := sorry

end AlgebraicGeometry.RingedSpace.ClosedSubset

