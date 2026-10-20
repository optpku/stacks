/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.SheafComparison

@[expose] public section

universe u

/- Lemma 95.14.10. Viewing an algebraic-space torsor as its sheaf of points is an
 equivalence of stacks in groupoids over the fppf site. -/
@[stacks 04UT] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.Classifying.toSheafHom_isEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupAlgebraicSpace B),
      CategoryTheory.StackOver.Groupoids.Hom.IsEquivalence
        (AlgebraicGeometry.GroupAlgebraicSpace.Classifying.toSheafHom G))
