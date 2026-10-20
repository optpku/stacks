module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Restriction

open CategoryTheory
open scoped AlgebraicGeometry

universe u

#check (@AlgebraicGeometry.FormallyUnramified.resLE :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) [AlgebraicGeometry.FormallyUnramified f],
      AlgebraicGeometry.FormallyUnramified (f.resLE V U e))
