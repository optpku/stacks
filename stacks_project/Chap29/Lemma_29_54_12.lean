module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.Unibranch

universe u

/- Lemma 29.54.12

Let `X` be an irreducible, geometrically unibranch scheme. The normalization morphism
`X.normalizationTo : X.normalization ⟶ X` is a universal homeomorphism.
-/
@[stacks 0GIQ] #check
  (AlgebraicGeometry.Scheme.universalHomeomorphism_normalizationTo :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [IrreducibleSpace X],
      X.isGeometricallyUnibranch →
        AlgebraicGeometry.UniversalHomeomorphism X.normalizationTo)
