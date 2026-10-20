module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.Lift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Stalks of finite pushforwards on algebraic spaces

The geometric stalk of a finite pushforward is the product of the stalks over the
same-field geometric fiber.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The geometric stalk of the pushforward of a set-valued small étale sheaf along a finite
morphism of algebraic spaces is isomorphic to the product of its stalks over the same-field
geometric fiber. -/
theorem finite_pushforward_stalk_product
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    (ybar : GeometricPoint Y) (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIsomorphic
      (GeometricPoint.stalk ybar ((sheafPushforwardType f).obj F).obj)
      ((x : CategoryTheory.Over.mk ybar.hom ⟶ CategoryTheory.Over.mk f) →
        GeometricPoint.stalk (GeometricPoint.ofHom ybar x.left) F.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
