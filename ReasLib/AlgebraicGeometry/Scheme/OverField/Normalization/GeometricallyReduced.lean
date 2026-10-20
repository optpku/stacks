module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.PointwiseRegular
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PointsOver
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Closure
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.LocallyNoetherian

/-!
# Geometric reducedness from normalization fibers

This leaf packages the separability condition on the residue fields in a
normalization fiber and its dimension-one geometric reducedness consequences.
The condition is independent of a particular curve or delta-invariant
application.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.Normalization

variable {k : Type u} [Field k]

namespace FiberResidues

/-- The residue fields in the normalization fiber above `x` are separable over
the base field. -/
def separableAt
    (X : SchemeOverField k) [LocallyAlgebraic X] (x : X.left) : Prop :=
  ∀ xν : X.left.normalizationTo.pointsOver x,
    Scheme.Hom.ResidueField.IsSeparableOverSpec
      (X.left.normalizationTo ≫ X.hom) xν

/-- Unfold separability of normalization-fiber residue fields above `x`. -/
theorem separableAt_iff
    (X : SchemeOverField k) [LocallyAlgebraic X] (x : X.left) :
    separableAt X x ↔
      ∀ xν : X.left.normalizationTo.pointsOver x,
        Scheme.Hom.ResidueField.IsSeparableOverSpec
          (X.left.normalizationTo ≫ X.hom) xν := sorry

/-- If the stalk of a locally algebraic scheme over a field is reduced and
one-dimensional, and the normalization-fiber residue fields are separable,
then the normalization morphism is geometrically regular at every point of
that fiber. -/
@[stacks 0C3P]
theorem geometricallyRegularAt_of_reduced_stalk_of_dimension_one
    (X : SchemeOverField k) [LocallyAlgebraic X] (x : X.left)
    [_root_.IsReduced (stalkRing X x)]
    (h_dimension : ringKrullDim (stalkRing X x) = 1)
    (h_separable : separableAt X x) :
    ∀ xν : X.left.normalizationTo.pointsOver x,
      Scheme.Hom.IsGeometricallyRegularAt (X.left.normalizationTo ≫ X.hom) xν := sorry

/-- If the stalk of a locally algebraic scheme over a field is reduced and
one-dimensional, and the normalization-fiber residue fields are separable,
then the scheme is geometrically reduced at that point. -/
@[stacks 0C3P]
theorem geometricallyReducedAt_of_reduced_stalk_of_dimension_one
    (X : SchemeOverField k) [LocallyAlgebraic X] (x : X.left)
    [_root_.IsReduced (stalkRing X x)]
    (h_dimension : ringKrullDim (stalkRing X x) = 1)
    (h_separable : separableAt X x) :
    SchemeOverField.geometricallyReducedAt X x := sorry

end FiberResidues

end AlgebraicGeometry.SchemeOverField.Normalization
