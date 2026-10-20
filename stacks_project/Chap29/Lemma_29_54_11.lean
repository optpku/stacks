/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.Nagata

universe u

/- Lemma 29.54.11
Let `X` be a Nagata scheme. The normalization morphism of `X` is finite.
-/
@[stacks 035S] #check
  (AlgebraicGeometry.Scheme.isFinite_normalizationTo_of_nagata :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.Nagata X],
      AlgebraicGeometry.IsFinite X.normalizationTo)
