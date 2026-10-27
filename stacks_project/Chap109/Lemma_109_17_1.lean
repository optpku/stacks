/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Smooth.Density
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 109.17.1 (1): the smooth-curve locus is open in the lci-plus point space. -/
@[stacks 0E86] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.isOpen_smoothPointsSet :
    ∀ S : Scheme.{u},
      IsOpen (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothPointsSet S))

/- Lemma 109.17.1 (2): the smooth-curve locus is dense in the lci-plus point space. -/
@[stacks 0E86] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.dense_smoothPointsSet :
    ∀ S : Scheme.{u},
      Dense (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothPointsSet S))
