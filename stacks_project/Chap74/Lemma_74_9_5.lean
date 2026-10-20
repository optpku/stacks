/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.ObjectProperty

universe u

variable (S : Scheme.{u})

/- Lemma 74.9.5 (1): Let `f : X ⟶ Y` be a smooth morphism of algebraic spaces.
If `Y` is reduced, then `X` is reduced. -/
@[stacks 0GB3] #check
  (AlgebraicGeometry.AlgebraicSpace.isReduced_inheritedFromTarget :
    InheritedFromTarget
      (AlgebraicGeometry.AlgebraicSpace.IsReduced : ObjectProperty (AlgebraicSpace S))
      (@AlgebraicGeometry.AlgebraicSpace.Smooth S : MorphismProperty (AlgebraicSpace S)))

/- Lemma 74.9.5 (2): Let `f : X ⟶ Y` be a surjective smooth morphism of algebraic
spaces. If `X` is reduced, then `Y` is reduced. -/
@[stacks 0GB3] #check
  (AlgebraicGeometry.AlgebraicSpace.isReduced_inheritedFromSource :
    InheritedFromSource
      (AlgebraicGeometry.AlgebraicSpace.IsReduced : ObjectProperty (AlgebraicSpace S))
      ((@AlgebraicGeometry.AlgebraicSpace.Smooth S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@AlgebraicGeometry.AlgebraicSpace.Surjective S : MorphismProperty (AlgebraicSpace S))))

#check (AlgebraicGeometry.AlgebraicSpace.IsReduced.of_smooth :
  ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Smooth f]
    [AlgebraicGeometry.AlgebraicSpace.IsReduced Y],
    AlgebraicGeometry.AlgebraicSpace.IsReduced X)

#check (AlgebraicGeometry.AlgebraicSpace.IsReduced.of_smooth_surjective :
  ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Smooth f]
    [AlgebraicGeometry.AlgebraicSpace.Surjective f]
    [AlgebraicGeometry.AlgebraicSpace.IsReduced X],
    AlgebraicGeometry.AlgebraicSpace.IsReduced Y)
