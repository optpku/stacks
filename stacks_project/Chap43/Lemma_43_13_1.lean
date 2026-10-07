module

import Mathlib.Analysis.Complex.Polynomial.Basic
import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension
import ReasLib.AlgebraicGeometry.Scheme.Variety.Product
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable (X Y : SchemeOverField ℂ) [Variety X] [Variety Y]

/- Lemma 43.13.1 (1): the fibre product over `Spec ℂ` of two complex varieties is a
variety. -/
@[stacks 0AZM] #check
  (AlgebraicGeometry.instVarietyPullbackOverSpecOfVarieties X Y :
    Variety (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)))

/- Lemma 43.13.1 (2): the topological Krull dimension of the fibre product over `Spec ℂ`
of two complex varieties is the sum of their dimensions. -/
@[stacks 0AZM] #check
  (AlgebraicGeometry.SchemeOverField.topologicalKrullDim_pullback_eq_add X Y :
    topologicalKrullDim (pullback X.hom Y.hom : Scheme) =
      topologicalKrullDim X.left + topologicalKrullDim Y.left)
