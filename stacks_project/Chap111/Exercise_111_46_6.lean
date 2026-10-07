module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap111.Exercise_111_46_2_Coincidence
public import stacks_project.Chap111.Exercise_111_46_4_PointSum
public import stacks_project.Chap111.Exercise_111_46_6_Effective

/-!
# Closed points of the difference-effective locus on `X^r × X^s`

The closed-point characterisation of the locus of tuples whose point-sum
difference is linearly equivalent to an effective divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.IdealSheafData
open CategoryTheory.MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry MonoidalCategory

universe u

namespace AlgebraicGeometry.Curve

/-- Exercise 111.46.6: let `k` be an algebraically closed field, let `X` be a
smooth projective curve over `k`, and let `r ≥ s` be natural numbers. There is a
natural closed subset `Z ⊂ X^r × X^s` whose closed points
`(x 1, …, x r, y 1, …, y s)` are exactly those for which the divisor
`x 1 + ⋯ + x r - y 1 - ⋯ - y s` is linearly equivalent to an effective divisor. -/
@[stacks 0EGE]
theorem exists_differenceEffectiveLocus
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Projective X.hom] [Smooth X.hom]
    (r s : ℕ) (hs : s ≤ r) :
    ∃ Z : (tensorPower X r ⊗ tensorPower X s).left.IdealSheafData,
      ∀ {x : Fin r → X.left} (hx : ∀ i, x i ∈ closedPoints X.left)
        {y : Fin s → X.left} (hy : ∀ j, y j ∈ closedPoints X.left)
        {z : (tensorPower X r ⊗ tensorPower X s).left}
        (hz : z ∈ closedPoints (tensorPower X r ⊗ tensorPower X s).left),
        (∀ i, (fst (tensorPower X r) (tensorPower X s) ≫ coord X r i).left.base z = x i) →
          (∀ j, (snd (tensorPower X r) (tensorPower X s) ≫ coord X s j).left.base z = y j) →
            (z ∈ Z.support ↔
              differenceLinearlyEquivalentToEffective
                (pointSumDivisor X x hx) (pointSumDivisor X y hy)) :=
  sorry

end AlgebraicGeometry.Curve
