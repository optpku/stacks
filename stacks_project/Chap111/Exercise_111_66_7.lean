module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology.HyperellipticDegree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/- Exercise 111.66.7: let `X` be a smooth projective curve over an algebraically closed
field of genus `g ≥ 100`. As `ℒ` ranges over invertible `𝒪_X`-modules of degree
`2 * genus X - 4`, the values of `Scheme.Hom.cohomologyFinrank X.hom ℒ 0` are exactly
`genus X - 3` and `genus X - 2`, together with `genus X - 1` if and only if `X` is
hyperelliptic. -/
@[stacks 0H8W]
#check (AlgebraicGeometry.Curve.exists_cohomologyFinrank_eq_iff_of_degree_two_mul_genus_sub_four :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
    (hgenus : 100 ≤ genus X) (n : ℕ),
    (∃ (L : X.left.Modules) (hL : Scheme.Modules.Invertible L),
        @Scheme.Modules.curveDegreeOfInvertible k _ X.left X.hom _
            topologicalKrullDim_eq_one.le L hL =
          (2 * genus X - 4 : ℤ) ∧
        Scheme.Hom.cohomologyFinrank X.hom L 0 = n) ↔
      n = genus X - 3 ∨ n = genus X - 2 ∨
        (n = genus X - 1 ∧ IsHyperelliptic X))

/- An invertible module of degree `2 * genus X - 4` on a smooth projective curve of
genus at least `100` has global-section dimension `genus X - 3`, `genus X - 2`, or
`genus X - 1`. -/
#check (AlgebraicGeometry.Curve.cohomologyFinrank_eq_of_degree_two_mul_genus_sub_four :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
    (hgenus : 100 ≤ genus X) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (hdeg : Scheme.Modules.curveDegreeOfInvertible X.hom
        topologicalKrullDim_eq_one.le L = (2 * genus X - 4 : ℤ)),
    Scheme.Hom.cohomologyFinrank X.hom L 0 = genus X - 3 ∨
      Scheme.Hom.cohomologyFinrank X.hom L 0 = genus X - 2 ∨
        Scheme.Hom.cohomologyFinrank X.hom L 0 = genus X - 1)

end AlgebraicGeometry.Curve
