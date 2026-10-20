/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal.Locality
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Lemma 74.20.2 (1): a property of morphisms of algebraic spaces over a scheme
`S` that is smooth local on source-and-target is smooth local on the source. -/
@[stacks 06F9] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget.toIsLocalAtSource :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsSmoothLocalAtSourceAndTarget P],
      P.IsLocalAtSource (precoverage (@Smooth S)))

/- Lemma 74.20.2 (2): a property of morphisms of algebraic spaces over a scheme
`S` that is smooth local on source-and-target is smooth local on the target. -/
@[stacks 06F9] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget.toIsLocalAtTarget :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsSmoothLocalAtSourceAndTarget P],
      P.IsLocalAtTarget (precoverage (@Smooth S)))

/- Lemma 74.20.2 (3): a property of morphisms of algebraic spaces over a scheme
`S` that is smooth local on source-and-target is stable under postcomposition
with smooth morphisms. -/
@[stacks 06F9] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSmoothLocalAtSourceAndTarget.toRespectsRightSmooth :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [IsSmoothLocalAtSourceAndTarget P],
      P.RespectsRight (@Smooth S : MorphismProperty (AlgebraicSpace S)))
