/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Nagata
import StacksCheckRecall

universe u

/- Lemma 67.49.9
Let `S` be a scheme, and let `X` be a Nagata algebraic space
over `S`. Then the absolute normalization `ν : X^ν ⟶ X`, namely
`X.normalizationTo : X.normalization ⟶ X`, is finite.
-/
@[stacks 0BB5] #check
  (AlgebraicGeometry.AlgebraicSpace.instIsFiniteNormalizationToOfIsNagata :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      [AlgebraicGeometry.AlgebraicSpace.IsNagata X] →
        AlgebraicGeometry.AlgebraicSpace.IsFinite X.normalizationTo)
