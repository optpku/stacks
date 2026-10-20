/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Normalization
import StacksCheckRecall

universe u

open CategoryTheory

/- Lemma 29.53.8: if `f : Y ⟶ X` is quasi-compact and quasi-separated and `Y` is reduced,
then the relative normalization of `X` in `Y` is reduced. -/
@[stacks 0AXN] #check
  (AlgebraicGeometry.Scheme.Hom.instIsReducedNormalization :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      [AlgebraicGeometry.IsReduced Y],
      AlgebraicGeometry.IsReduced f.normalization)
