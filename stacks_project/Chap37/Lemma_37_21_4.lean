/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Regular.Locality
import StacksCheckRecall

universe u

/- Lemma 37.21.4 (1): the property that the fibres of a scheme morphism are locally
Noetherian and the morphism is regular is local in the fppf topology on the target. -/
@[stacks 07RA] #check
  (AlgebraicGeometry.LocallyNoetherianRegular.isLocalAtTargetFppf :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓ @AlgebraicGeometry.Regular) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)

/- Lemma 37.21.4 (2): the property that the fibres of a scheme morphism are locally
Noetherian and the morphism is regular is local in the smooth topology on the source. -/
@[stacks 07RA] #check
  (AlgebraicGeometry.LocallyNoetherianRegular.isLocalAtSourceSmooth :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      ((AlgebraicGeometry.LocallyNoetherianFibers ⊓ @AlgebraicGeometry.Regular) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage)
