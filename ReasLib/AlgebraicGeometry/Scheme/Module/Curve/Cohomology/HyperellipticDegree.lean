module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Hyperelliptic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- On a smooth projective curve over an algebraically closed field of genus at least `100`,
the global-section dimensions of invertible modules of degree `2 * genus X - 4` are exactly
`genus X - 3` and `genus X - 2`, together with `genus X - 1` precisely when the curve is
hyperelliptic. -/
theorem exists_cohomologyFinrank_eq_iff_of_degree_two_mul_genus_sub_four
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
    (hgenus : 100 ≤ genus X) (n : ℕ) :
    (∃ (L : X.left.Modules) (hL : Scheme.Modules.Invertible L),
        @Scheme.Modules.curveDegreeOfInvertible k _ X.left X.hom _
            topologicalKrullDim_eq_one.le L hL =
          (2 * genus X - 4 : ℤ) ∧
        Scheme.Hom.cohomologyFinrank X.hom L 0 = n) ↔
      n = genus X - 3 ∨ n = genus X - 2 ∨
        (n = genus X - 1 ∧ IsHyperelliptic X) := sorry

/-- An invertible module of degree `2 * genus X - 4` on a smooth projective curve over an
algebraically closed field of genus at least `100` has global-section dimension
`genus X - 3`, `genus X - 2`, or `genus X - 1`. -/
theorem cohomologyFinrank_eq_of_degree_two_mul_genus_sub_four
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
    (hgenus : 100 ≤ genus X) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (hdeg : Scheme.Modules.curveDegreeOfInvertible X.hom
        topologicalKrullDim_eq_one.le L = (2 * genus X - 4 : ℤ)) :
    Scheme.Hom.cohomologyFinrank X.hom L 0 = genus X - 3 ∨
      Scheme.Hom.cohomologyFinrank X.hom L 0 = genus X - 2 ∨
        Scheme.Hom.cohomologyFinrank X.hom L 0 = genus X - 1 := sorry

end AlgebraicGeometry.Curve
