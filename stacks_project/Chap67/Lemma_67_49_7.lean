/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Reduction

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.49.7

Let `S` be a scheme and let `X` be an algebraic space over `S` satisfying the
equivalent conditions of Lemma 67.49.1. Its normalization morphism factors through
the reduction, and the resulting morphism is the normalization of the reduction.
-/
@[stacks 0BB3] #check
  (AlgebraicGeometry.AlgebraicSpace.Normalization.factorsThroughReduction :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens X],
      ∃ νred : X.normalization ⟶ X.reduction,
        νred ≫ X.reductionι = X.normalizationTo)

#check
  (AlgebraicGeometry.AlgebraicSpace.Normalization.reductionFactorIsNormalization :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens X]
      {νred : X.normalization ⟶ X.reduction},
      νred ≫ X.reductionι = X.normalizationTo →
        ∃ e : X.normalization ≅ X.reduction.normalization,
          νred = e.hom ≫ X.reduction.normalizationTo)
