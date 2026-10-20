/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
import StacksCheckRecall

universe u

/- Lemma 29.7.3: for a quasi-compact open immersion, scheme-theoretic density
is equivalent to the canonical immersion of the scheme-theoretic closure being
an isomorphism, so the closure is the whole ambient scheme. -/
@[stacks 01RD] #check
  (AlgebraicGeometry.schemeTheoreticallyDense_iff_isIso_schemeTheoreticClosureι :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens)
      [AlgebraicGeometry.QuasiCompact U.ι],
      AlgebraicGeometry.schemeTheoreticallyDense U ↔
        CategoryTheory.IsIso (AlgebraicGeometry.schemeTheoreticClosureι U))
