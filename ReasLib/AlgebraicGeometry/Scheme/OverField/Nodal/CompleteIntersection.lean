module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.CompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry RelativeDerivation

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A locally algebraic, equidimensional scheme of dimension one over a field has
at-worst-nodal singularities exactly when it is a local complete intersection and
the closed subscheme cut out by the first Fitting ideal of its relative differentials
is unramified over the field. -/
theorem atWorstNodal_iff_localCompleteIntersection_and_unramified_firstFitting
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1) :
    atWorstNodal X ↔
      IsLocalCompleteIntersectionOver k X.hom ∧
        Unramified ((Scheme.fittingIdealSheaf (Ω[X.hom.toShHom]) 1).subschemeι ≫ X.hom) := sorry

end AlgebraicGeometry.SchemeOverField
