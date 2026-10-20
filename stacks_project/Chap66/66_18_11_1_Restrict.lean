module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.Types

/-!
# Weak sheafification on the small étale topology

Type-valued sheaves on the small étale site of an algebraic space admit weak
sheafification, which is the existence hypothesis for cocontinuous inverse image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology_hasWeakSheafify :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    HasWeakSheafify (smallEtaleTopology X) (Type u))

