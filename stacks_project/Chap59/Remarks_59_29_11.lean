/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Points.Conservative

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.GeometricPoint

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable (S : Scheme.{u})

/- Remarks 59.29.11 (1): the small étale points associated to geometric points
form a conservative family. -/
@[stacks 040S] #check
  (AlgebraicGeometry.Scheme.GeometricPoint.geometricPointFamily_isConservative :
    ∀ S : Scheme.{u}, (geometricPointFamily S).IsConservativeFamilyOfPoints)

/- The small étale site has enough points. -/
#check (CategoryTheory.GrothendieckTopology.HasEnoughPoints.exists_objectProperty
    (smallEtaleTopology S) :
    ∃ P : ObjectProperty (GrothendieckTopology.Point.{u} (smallEtaleTopology S)),
      ObjectProperty.Small.{u} P ∧ P.IsConservativeFamilyOfPoints)

/- If `F` is a sheaf on the big étale site of `S` and
`t` is a geometric point of an object `T ⟶ S`, the stalk `F` at `t` is the
small-étale stalk of the restriction of `F` to `T.Etale`. -/
#check (AlgebraicGeometry.Scheme.GeometricPoint.bigEtaleStalk :
    ∀ {S T : Scheme.{u}}, Sheaf (S.overGrothendieckTopology @Etale) (Type u) →
      GeometricPoint T → (T ⟶ S) → Type u)

/- The big étale site of `S` has enough points, by
considering all geometric points of all objects of this site. -/
#check (AlgebraicGeometry.Scheme.Etale.instHasEnoughPointsBig :
    ∀ S : Scheme.{u}, GrothendieckTopology.HasEnoughPoints.{u + 1}
      (S.overGrothendieckTopology @Etale))

end AlgebraicGeometry.Scheme.GeometricPoint
