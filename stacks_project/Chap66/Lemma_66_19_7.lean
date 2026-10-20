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

/- Lemma 66.19.7 (1): let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`xbar` be a geometric point of `X`. The functor `u : X_étale ⥤ Type` sending `U` to `|U_xbar|`,
equivalently the Hom-lifts of `xbar` through `U`, is the fiber of a point `p` of the site
`X_étale` (Sites, Definition 7.32.2). -/
@[stacks 04K0] #check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.toSmallEtalePoint :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    AlgebraicSpace.GeometricPoint X → (AlgebraicSpace.smallEtaleTopology X).Point.{u})

/- Lemma 66.19.7 (2): the associated stalk functor `F ↦ F_p` (Sites, Equation 7.32.1.1) is
the geometric stalk functor `F ↦ F_xbar` of Definition 66.19.6. -/
@[stacks 04K0] #check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.toSmallEtalePoint_stalkIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : AlgebraicSpace.GeometricPoint X),
    ((AlgebraicSpace.GeometricPoint.toSmallEtalePoint xbar).presheafFiber :
      ((AlgebraicSpace.smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) ⥤ Type (u + 1)) ≅
      AlgebraicSpace.GeometricPoint.stalkFunctor xbar)
