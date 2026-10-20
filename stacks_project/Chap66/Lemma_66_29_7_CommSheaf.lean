module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing

/-!
Compatibility import for the canonical commutative small-étale structure sheaf.
The tagged module source statement retains its original specialization.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.commStructureSheaf :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.Sheaf (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X) CommRingCat.{u})
