module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LinearEquivalence.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.PointSum
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.TensorPower.Coordinates
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

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

/-- For a smooth projective curve over an algebraically closed field and natural
numbers `r ≥ s`, there is a closed locus in `X^r × X^s` whose closed points are
precisely the pairs of tuples whose point-sum difference is linearly equivalent
to an effective divisor, with repeated points counted with multiplicity. -/
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
