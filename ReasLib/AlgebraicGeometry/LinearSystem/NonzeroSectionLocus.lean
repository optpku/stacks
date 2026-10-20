/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.PointSum
public import ReasLib.AlgebraicGeometry.Scheme.Module.NegTwist
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.TensorPower.Coordinates
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Closed points of the negative-twist section locus on `X^r`

The closed-point characterisation of the locus of tuples whose point-sum
negative twist of an invertible module has a nonzero global section.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

/-- For an invertible module on a smooth projective curve over an algebraically
closed field and any natural number `r`, there is a closed locus in `X^r` whose
closed points are precisely the tuples for which the negative twist by the
point-sum divisor has a nonzero global section, with repeated points counted
with multiplicity. -/
theorem exists_negTwistHasNonzeroSectionLocus
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Projective X.hom] [Smooth X.hom]
    (L : X.left.Modules) [Invertible L] (r : ℕ) :
    ∃ Z : (tensorPower X r).left.IdealSheafData,
      ∀ {x : Fin r → X.left} (hx : ∀ i, x i ∈ closedPoints X.left)
        {z : (tensorPower X r).left}
        (hz : z ∈ closedPoints (tensorPower X r).left),
        (∀ i, (coord X r i).left.base z = x i) →
          (z ∈ Z.support ↔
            ∃ s : (negTwist L (pointSumDivisor X x hx)).sections,
              (negTwist L (pointSumDivisor X x hx)).unitHomEquiv.symm s ≠ 0) :=
  sorry

end AlgebraicGeometry.Curve
