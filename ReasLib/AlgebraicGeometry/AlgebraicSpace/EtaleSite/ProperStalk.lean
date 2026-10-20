module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GeometricFiberSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ProperBaseChange

/-!
# Proper base change for geometric stalks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a proper morphism of algebraic spaces, the canonical map from a geometric
stalk of the small étale pushforward to global sections of the inverse-image sheaf
on the geometric fibre is bijective. -/
@[stacks 0DG1]
theorem smallEtalePushforwardStalk_bijective_of_proper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) [Proper f]
    (xbar : GeometricPoint X)
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    Function.Bijective
      (smallEtalePushforwardStalkToGeometricFiberSections f xbar F) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace
