module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Lattice
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FiniteSeparableCoproduct
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A reduced equidimensional one-dimensional closed subscheme of a locally algebraic
equidimensional one-dimensional at-worst-nodal scheme is at-worst-nodal. -/
theorem atWorstNodal_of_reducedClosedSubscheme
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left]
    (hXdim : topologicalKrullDim X.left = 1) (hXnodal : atWorstNodal X)
    (Y : X.left.IdealSheafData) [IsReduced Y.subscheme]
    [EquidimensionalSpace Y.subscheme]
    (hYdim : topologicalKrullDim Y.subscheme = 1) :
    atWorstNodal (Over.mk (Y.subschemeι ≫ X.hom)) := sorry

/-- The scheme-theoretic intersection of a reduced equidimensional one-dimensional closed
subscheme of a locally algebraic equidimensional one-dimensional at-worst-nodal scheme
with the closure of its open complement is a disjoint union of spectra of finite separable
extensions of the base field. -/
theorem intersection_isDisjointUnionOfSpecFiniteSeparable
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left]
    (hXdim : topologicalKrullDim X.left = 1) (hXnodal : atWorstNodal X)
    (Y : X.left.IdealSheafData) [IsReduced Y.subscheme]
    [EquidimensionalSpace Y.subscheme]
    (hYdim : topologicalKrullDim Y.subscheme = 1) :
    Nonempty
      (SchemeAsDisjointUnionOfSpecFiniteSeparable k
        (Over.mk
          ((Y ⊔ schemeTheoreticClosureIdeal Y.openComplement).subschemeι ≫ X.hom))) := sorry

/-- Every point of the scheme-theoretic intersection of a reduced equidimensional
one-dimensional closed subscheme of a locally algebraic equidimensional one-dimensional
at-worst-nodal scheme with the closure of its open complement is a node of the ambient scheme. -/
theorem intersection_points_areNodes
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left]
    (hXdim : topologicalKrullDim X.left = 1) (hXnodal : atWorstNodal X)
    (Y : X.left.IdealSheafData) [IsReduced Y.subscheme]
    [EquidimensionalSpace Y.subscheme]
    (hYdim : topologicalKrullDim Y.subscheme = 1) :
    ∀ p : (Y ⊔ schemeTheoreticClosureIdeal Y.openComplement).subscheme,
      isNode X ((Y ⊔ schemeTheoreticClosureIdeal Y.openComplement).subschemeι p) := sorry

/-- A reduced equidimensional one-dimensional closed subscheme of a locally algebraic
equidimensional one-dimensional at-worst-nodal scheme is smooth over the base field at
every point of its scheme-theoretic intersection with the closure of its open complement. -/
theorem smoothAt_intersectionPoints
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    [EquidimensionalSpace X.left]
    (hXdim : topologicalKrullDim X.left = 1) (hXnodal : atWorstNodal X)
    (Y : X.left.IdealSheafData) [IsReduced Y.subscheme]
    [EquidimensionalSpace Y.subscheme]
    (hYdim : topologicalKrullDim Y.subscheme = 1) :
    ∀ p : (Y ⊔ schemeTheoreticClosureIdeal Y.openComplement).subscheme,
      (Y.subschemeι ≫ X.hom).SmoothAt
        ((Scheme.IdealSheafData.inclusion
          (le_sup_left : Y ≤ Y ⊔ schemeTheoreticClosureIdeal Y.openComplement)) p) := sorry

end AlgebraicGeometry.SchemeOverField
