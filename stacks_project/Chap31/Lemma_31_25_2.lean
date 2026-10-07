module

import ReasLib.AlgebraicGeometry.Scheme.Normalization.MeromorphicFunction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 31.25.2: for a reduced scheme whose quasi-compact opens have finitely many irreducible
components, the normalization morphism is the relative spectrum of the integral closure of the
structure sheaf in the sheaf of meromorphic functions. -/
@[stacks 035T] #check
  (AlgebraicGeometry.Scheme.Normalization.MeromorphicFunction.normalizationTo_restrict_isIsomorphic_integralClosureSpec :
    ∀ (X : Scheme.{u}) [IsReduced X]
      [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] (U : X.affineOpens),
      IsIsomorphic (Over.mk (X.normalizationTo ∣_ (U : X.Opens)))
        (Over.mk (AlgebraicGeometry.Scheme.Normalization.MeromorphicFunction.integralClosureSpecToAffineOpen X U)))
