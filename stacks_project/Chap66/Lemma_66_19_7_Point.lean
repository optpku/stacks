/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 66.19.7: the lift-valued fiber of the geometric site point agrees naturally with
its small étale neighborhood presentation. -/
@[stacks 04K0] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.toSmallEtalePoint_fiberIso_smallLiftFunctor :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : AlgebraicSpace.GeometricPoint X),
      (AlgebraicSpace.GeometricPoint.toSmallEtalePoint xbar).fiber ≅
        AlgebraicSpace.GeometricPoint.smallLiftFunctor xbar)

#check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.toSmallEtalePoint_stalkEquiv :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : AlgebraicSpace.GeometricPoint X)
    (F : (AlgebraicSpace.smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)),
    ((AlgebraicSpace.GeometricPoint.toSmallEtalePoint xbar).presheafFiber :
      ((AlgebraicSpace.smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) ⥤ Type (u + 1)).obj F ≃
      AlgebraicSpace.GeometricPoint.stalk xbar F)
