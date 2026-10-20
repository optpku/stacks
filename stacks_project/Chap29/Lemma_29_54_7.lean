/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.FiniteComponents

universe u

/- Lemma 29.54.7: let `X` be a reduced scheme with finitely many irreducible components. Then
the normalization morphism `X.normalizationTo` is birational. -/
@[stacks 0BXC] #check
  (AlgebraicGeometry.Scheme.Normalization.isBirational_of_isReduced_finiteComponents :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [Finite (irreducibleComponents X)],
      AlgebraicGeometry.IsBirational X.normalizationTo)
