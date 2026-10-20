/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianFibers
import StacksCheckRecall

universe u

/- Lemma 37.20.4 (1): the property that the fibres of a scheme morphism are locally
Noetherian is local in the fppf topology on the source. -/
@[stacks 0392] #check
  (AlgebraicGeometry.LocallyNoetherianFibers.isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (AlgebraicGeometry.LocallyNoetherianFibers :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)

/- Lemma 37.20.4 (2): the property that the fibres of a scheme morphism are locally
Noetherian is local in the fppf topology on the target. -/
@[stacks 0392] #check
  (AlgebraicGeometry.LocallyNoetherianFibers.isLocalAtTargetFppf :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (AlgebraicGeometry.LocallyNoetherianFibers :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
