/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure.Reduced
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 29.7.9 (1): if `U ⊆ X` is a reduced open subscheme, then its scheme-theoretic
closure is `X` exactly when `U` is scheme-theoretically dense in `X`. -/
@[stacks 056E] #check
  (AlgebraicGeometry.schemeTheoreticClosure_eq_self_iff_schemeTheoreticallyDense_of_isReduced :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens)
      [AlgebraicGeometry.IsReduced U.toScheme],
      AlgebraicGeometry.schemeTheoreticClosure U = X ↔
        AlgebraicGeometry.schemeTheoreticallyDense U)

/- Lemma 29.7.9 (2): if `U ⊆ X` is a reduced open subscheme whose scheme-theoretic
closure is `X`, then `X` is reduced. -/
@[stacks 056E] #check
  (AlgebraicGeometry.isReduced_of_schemeTheoreticClosure_eq_self_of_isReduced :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens)
      [AlgebraicGeometry.IsReduced U.toScheme],
      AlgebraicGeometry.schemeTheoreticClosure U = X → AlgebraicGeometry.IsReduced X)
