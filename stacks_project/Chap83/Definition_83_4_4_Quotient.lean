module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.UniversalCategoricalQuotient

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/- A typed compatibility check keeps this import path available to downstream sources. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.baseChange :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X X' : Over B}
      (P : PreRelation U) {φ : U ⟶ X}, P.IsInvariantHom φ →
        (f : X' ⟶ X) → PreRelation (pullback φ f))

end AlgebraicGeometry.AlgebraicSpace.PreRelation
