module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction

/-! Compatibility facade for the actual meromorphic-function sheaf. -/

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.meromorphicFunctionSheaf :
    {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.AlgebraicSpace S) →
      CategoryTheory.Sheaf (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X)
        CommRingCat.{u + 1})
