/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular.Singleton
import StacksCheckRecall

/-!
# Reduced locally Noetherian singleton algebraic spaces are regular

A reduced, locally Noetherian algebraic space whose space of points is a
singleton is regular.
-/

@[expose] public section

universe u

/- Lemma 68.13.8: A reduced, locally Noetherian algebraic space `Z` whose space of
points is a singleton is regular. -/
@[stacks 06R1]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsRegular.of_singleton_points :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (Z : AlgebraicGeometry.AlgebraicSpace S)
      [AlgebraicGeometry.AlgebraicSpace.IsReduced Z]
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian Z]
      [Nonempty (AlgebraicGeometry.AlgebraicSpace.Points Z)]
      [Subsingleton (AlgebraicGeometry.AlgebraicSpace.Points Z)],
      AlgebraicGeometry.AlgebraicSpace.IsRegular Z)
