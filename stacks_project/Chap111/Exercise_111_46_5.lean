/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LinearSystem.NonzeroSectionLocus
import StacksCheckRecall

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

/- Exercise 111.46.5: let `k` be an algebraically closed field, let `X` be a
smooth projective curve over `k`, and let `L` be an invertible `𝒪_X`-module.
There is a natural closed subset `Z ⊂ X^r` whose closed points `(x 1, …, x r)`
are exactly those for which `L(-x 1 - ⋯ - x r)` has a nonzero global section. -/
@[stacks 0EGD] #check (AlgebraicGeometry.Curve.exists_negTwistHasNonzeroSectionLocus :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Curve X] [Projective X.hom] [Smooth X.hom]
    (L : X.left.Modules) [Invertible L] (r : ℕ),
    ∃ Z : (tensorPower X r).left.IdealSheafData,
      ∀ {x : Fin r → X.left} (hx : ∀ i, x i ∈ closedPoints X.left)
        {z : (tensorPower X r).left}
        (hz : z ∈ closedPoints (tensorPower X r).left),
        (∀ i, (coord X r i).left.base z = x i) →
          (z ∈ Z.support ↔
            ∃ s : (negTwist L (pointSumDivisor X x hx)).sections,
              (negTwist L (pointSumDivisor X x hx)).unitHomEquiv.symm s ≠ 0))

end AlgebraicGeometry.Curve
