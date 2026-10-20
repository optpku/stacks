/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions

/-!
# Source object properties imply relative morphism properties

If the source of a morphism of algebraic spaces is decent, reasonable, or has
property (β), then the morphism itself has the corresponding relative property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 68.17.3: a morphism from a decent algebraic space is decent. -/
@[stacks 0ABX] #check (AlgebraicGeometry.AlgebraicSpace.Decent.of_isDecent :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicSpace.IsDecent X],
    AlgebraicSpace.Decent f)

#check (AlgebraicGeometry.AlgebraicSpace.Reasonable.of_isReasonable :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicSpace.IsReasonable X],
    AlgebraicSpace.Reasonable f)

#check (AlgebraicGeometry.AlgebraicSpace.PropertyBeta.of_hasPropertyBeta :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [AlgebraicSpace.HasPropertyBeta X],
    AlgebraicSpace.PropertyBeta f)
