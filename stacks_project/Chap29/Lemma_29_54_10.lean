module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.Japanese

universe u

/- Lemma 29.54.10: the normalization morphism of an integral Japanese scheme is finite. -/
@[stacks 035R] #check
  (AlgebraicGeometry.Scheme.isFinite_normalizationTo_of_isJapanese :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X],
      AlgebraicGeometry.Scheme.IsJapanese X →
        AlgebraicGeometry.IsFinite X.normalizationTo)
