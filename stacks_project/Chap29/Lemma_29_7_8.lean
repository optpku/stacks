/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure.Reduced
import StacksCheckRecall

universe u

/- Lemma 29.7.8: for an open subscheme `U ⊆ X` of a reduced scheme `X`, topological density,
equality of the scheme-theoretic closure with `X`, and scheme-theoretic density are equivalent. -/
@[stacks 056D] #check
  (AlgebraicGeometry.SchemeTheoreticClosure.density_tfae_of_isReduced :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsReduced X] (U : X.Opens),
      List.TFAE [Dense (U : Set X), AlgebraicGeometry.schemeTheoreticClosure U = X,
        AlgebraicGeometry.schemeTheoreticallyDense U])
