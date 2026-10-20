/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular.EtaleLocalRing

universe u

/- Lemma 66.25.1: A locally Noetherian algebraic space is regular if and only if every
étale local ring at a geometric point is a regular local ring. -/
@[stacks 06LQ] #check
  (AlgebraicGeometry.AlgebraicSpace.isRegular_iff_forall_etaleLocalRing :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X],
      AlgebraicGeometry.AlgebraicSpace.IsRegular X ↔
        ∀ xbar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint X,
          IsRegularLocalRing (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing X xbar))
