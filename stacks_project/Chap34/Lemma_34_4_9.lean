/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation.Affine
import stacks_project.Chap34.Definition_34_4_8

universe u v

/- Lemma 34.4.9: For every chosen big étale presentation `X` and object
`S : X.carrier`, the inherited small étale carrier is a site. -/
@[stacks 021C] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.smallTopology :
    (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigEtaleSite.smallSite X S))

/- For every chosen big étale presentation `X` and object `S : X.carrier`,
the big affine étale carrier is a site. -/
#check
  (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineTopology :
    (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineSite X S))

/- For every chosen big étale presentation `X` and object `S : X.carrier`,
the small affine étale carrier is a site. -/
#check
  (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineTopology :
    (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineSite X S))
