module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth

/-!
# Étale morphisms of algebraic spaces are smooth
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale morphism of algebraic spaces is smooth. -/
instance smooth_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : Smooth f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
