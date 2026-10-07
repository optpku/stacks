module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.GeometricallyReduced
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.27.6 (1): a locally algebraic scheme over a field is geometrically
reduced at a point whose stalk is reduced and one-dimensional when every
normalization-fiber residue field above that point is separable. -/
@[stacks 0C3P] #check
  (AlgebraicGeometry.SchemeOverField.Normalization.FiberResidues.geometricallyReducedAt_of_reduced_stalk_of_dimension_one :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] (x : X.left)
      [_root_.IsReduced (AlgebraicGeometry.SchemeOverField.stalkRing X x)],
      ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x) = 1 →
        AlgebraicGeometry.SchemeOverField.Normalization.FiberResidues.separableAt X x →
          AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x)

/- Lemma 33.27.6 (2): under the same hypotheses, the normalization is
geometrically regular at every point above the chosen point. -/
@[stacks 0C3P] #check
  (AlgebraicGeometry.SchemeOverField.Normalization.FiberResidues.geometricallyRegularAt_of_reduced_stalk_of_dimension_one :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] (x : X.left)
      [_root_.IsReduced (AlgebraicGeometry.SchemeOverField.stalkRing X x)],
      ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x) = 1 →
        AlgebraicGeometry.SchemeOverField.Normalization.FiberResidues.separableAt X x →
          ∀ xν : X.left.normalizationTo.pointsOver x,
            AlgebraicGeometry.Scheme.Hom.IsGeometricallyRegularAt
              (X.left.normalizationTo ≫ X.hom) xν)
