/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Regular
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.62.11: A locally finite-type morphism between regular schemes is a local
complete intersection morphism. -/
@[stacks 0E9K] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isLocalCompleteIntersection_of_regular :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.Scheme.Regular X]
      [AlgebraicGeometry.Scheme.Regular Y],
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f)
