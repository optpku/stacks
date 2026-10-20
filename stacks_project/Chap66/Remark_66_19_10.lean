/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GeometricPointSections
import StacksCheckRecall

open CategoryTheory

universe u

/- Remark 66.19.10. The stalk at a geometric point is geometric inverse image
followed by global sections on the source-field spectrum. -/
@[stacks 04K3] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.stalkFunctorIsoPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.AlgebraicSpace S}
      (xbar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint X),
      ((AlgebraicGeometry.AlgebraicSpace.GeometricPoint.toSmallEtalePoint xbar).sheafFiber :
        CategoryTheory.Sheaf (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology X)
          (Type (u + 1)) ⥤ Type (u + 1)) ≅
        AlgebraicGeometry.AlgebraicSpace.GeometricPoint.pullbackThenSections xbar)
