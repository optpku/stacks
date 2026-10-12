/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A locally algebraic, equidimensional one-dimensional scheme with at-worst-nodal
singularities has a Gorenstein underlying scheme. -/
instance instGorensteinOfAtWorstNodal
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left] [Fact (topologicalKrullDim X.left = 1)]
    [Fact (atWorstNodal X)] : Scheme.Gorenstein X.left := sorry

/-- A locally algebraic, equidimensional one-dimensional scheme with at-worst-nodal
singularities is geometrically reduced over its base field. -/
instance instGeometricallyReducedOfAtWorstNodal
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left] [Fact (topologicalKrullDim X.left = 1)]
    [Fact (atWorstNodal X)] : GeometricallyReduced X.hom := sorry

end AlgebraicGeometry.SchemeOverField
