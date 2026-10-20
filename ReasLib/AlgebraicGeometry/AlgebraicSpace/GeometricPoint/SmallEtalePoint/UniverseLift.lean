/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint

/-!
# Universe-lifted small étale site points
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/-- The small étale site-point of a geometric point, with fiber values lifted to
`Type (u + 1)` so that `sheafModuleStalkFunctor` applies to `CommModules`. -/
def toSmallEtalePointSucc {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    (smallEtaleTopology X).Point.{u + 1} where
  fiber := (toSmallEtalePoint xbar).fiber ⋙ uliftFunctor.{u + 1, u}
  isCofiltered := sorry
  initiallySmall := sorry
  jointly_surjective := sorry

/-- The fiber of `toSmallEtalePointSucc` is the `ULift` of the ordinary small étale fiber. -/
theorem toSmallEtalePointSucc_fiber {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    (toSmallEtalePointSucc xbar).fiber =
      (toSmallEtalePoint xbar).fiber ⋙ uliftFunctor.{u + 1, u} :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
