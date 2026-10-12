/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
import StacksCheckRecall

universe u

/- Lemma 29.7.6: If `U` and `V` are scheme-theoretically dense open subschemes
of `X`, then so is their intersection. -/
@[stacks 01RF] #check
  (AlgebraicGeometry.schemeTheoreticallyDense_inf :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {U V : X.Opens},
      AlgebraicGeometry.schemeTheoreticallyDense U →
        AlgebraicGeometry.schemeTheoreticallyDense V →
          AlgebraicGeometry.schemeTheoreticallyDense (U ⊓ V))
