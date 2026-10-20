/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Big
public import ReasLib.CategoryTheory.Sites.Point.Universe
public import Mathlib.CategoryTheory.Sites.Point.Conservative

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

/-- The family of small étale site points associated to all geometric points
of a scheme. -/
def geometricPointFamily (S : Scheme.{u}) :
    ObjectProperty (GrothendieckTopology.Point.{u} (smallEtaleTopology S)) :=
  ObjectProperty.ofObj fun s : GeometricPoint S ↦ toSmallEtalePoint s

/-- A point belongs to the geometric-point family precisely when it is
associated to a geometric point of the scheme. -/
theorem mem_geometricPointFamily {S : Scheme.{u}}
    {p : GrothendieckTopology.Point.{u} (smallEtaleTopology S)} :
    geometricPointFamily S p ↔ ∃ s : GeometricPoint S, toSmallEtalePoint s = p := sorry

/-- The family of small étale points associated to all geometric points of a
scheme is conservative. -/
theorem geometricPointFamily_isConservative (S : Scheme.{u}) :
    (geometricPointFamily S).IsConservativeFamilyOfPoints := sorry

/-- The family of universe-lifted big étale points associated to all geometric
points of all schemes over the base. -/
def bigEtalePointFamily (S : Scheme.{u}) :
    ObjectProperty (GrothendieckTopology.Point.{u + 1}
      (S.overGrothendieckTopology @Etale)) :=
  ObjectProperty.ofObj fun point : Σ T : Over S, GeometricPoint T.left ↦
    (toBigEtalePoint point.2 point.1.hom).ulift

/-- A point belongs to the big étale family precisely when it is the lifted
point associated to a geometric point of an object over the base. -/
theorem mem_bigEtalePointFamily {S : Scheme.{u}}
    {p : GrothendieckTopology.Point.{u + 1} (S.overGrothendieckTopology @Etale)} :
    bigEtalePointFamily S p ↔
      ∃ (T : Over S) (t : GeometricPoint T.left),
        (toBigEtalePoint t T.hom).ulift = p := sorry

/-- The family of lifted big étale points coming from all geometric points of
all objects over the base is conservative. -/
theorem bigEtalePointFamily_isConservative (S : Scheme.{u}) :
    (bigEtalePointFamily S).IsConservativeFamilyOfPoints := sorry

end AlgebraicGeometry.Scheme.GeometricPoint

namespace AlgebraicGeometry.Scheme.Etale

/-- The big étale site admits a small conservative family of points with
fibers in `Type (u + 1)`. -/
theorem existsSmallConservativeBigPointFamily (S : Scheme.{u}) :
    ∃ P : ObjectProperty (GrothendieckTopology.Point.{u + 1}
      (S.overGrothendieckTopology @Etale)),
      ObjectProperty.Small.{u + 1} P ∧ P.IsConservativeFamilyOfPoints := sorry

/-- The big étale site has enough points with fibers in `Type (u + 1)`. -/
instance instHasEnoughPointsBig (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{u + 1}
      (S.overGrothendieckTopology @Etale) where
  exists_objectProperty := existsSmallConservativeBigPointFamily S

end AlgebraicGeometry.Scheme.Etale
