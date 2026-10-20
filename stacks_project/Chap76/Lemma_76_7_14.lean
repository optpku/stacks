/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.FiniteType

open CategoryTheory

universe u

/- Lemma 76.7.14: for a locally finite type morphism of algebraic spaces over a scheme,
the relative differential sheaf is a finite-type module sheaf on the source. -/
@[stacks 05ZE] #check
  (AlgebraicGeometry.AlgebraicSpace.isFiniteType_relativeDifferentials_of_locallyOfFiniteType :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f],
      (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDifferentials f).IsFiniteType)
