/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.AffineCriterion
import StacksCheckRecall

universe u

/- Lemma 66.3.4: An algebraic space is separated in the absolute sense if and only if every
pair of morphisms from affine schemes has affine fibre product and surjective canonical
ℤ-tensor map on global sections. -/
@[stacks 0AHS] #check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelySeparated.tfae :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.IsAbsolutelySeparated X,
      AlgebraicGeometry.AlgebraicSpace.forallAffinePullbackAffineSurjective X])
