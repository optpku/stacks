/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.GenericScaling
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

/- Remark 40.10.11 (1): Restricting the standard scaling-action groupoid on `𝔸¹_ℚ`
to the generic point `Spec(ℚ(x))` gives the explicit groupoid `GenericScaling.groupoid`. -/
@[stacks 04MR] #check
  (AlgebraicGeometry.GenericScaling.groupoid :
    AlgebraicGeometry.GroupoidScheme
      (AlgebraicGeometry.Spec (CommRingCat.of (ULift ℤ))))

/- Remark 40.10.11 (2): The object scheme of the restricted groupoid is `Spec(ℚ(x))`. -/
@[stacks 04MR] #check
  (AlgebraicGeometry.GenericScaling.groupoid_U :
    AlgebraicGeometry.GenericScaling.groupoid.U.left =
      AlgebraicGeometry.Spec (CommRingCat.of (RatFunc ℚ)))

/- Remark 40.10.11 (3): The arrow scheme has the affine presentation
`Spec(ℚ(x)[y][1/P(xy) | 0 ≠ P ∈ ℚ[T]])`. -/
@[stacks 04MR] #check
  (AlgebraicGeometry.GenericScaling.arrowIso :
    AlgebraicGeometry.GenericScaling.groupoid.R.left ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of AlgebraicGeometry.GenericScaling.arrowRing))

/- Remark 40.10.11 (4): The arrow scheme has topological Krull dimension one. -/
@[stacks 04MR] #check
  (AlgebraicGeometry.GenericScaling.arrowDimension :
    topologicalKrullDim AlgebraicGeometry.GenericScaling.groupoid.R.left = 1)

/- Remark 40.10.11 (5): The stabilizer of the generic point has topological Krull dimension
zero. -/
@[stacks 04MR] #check
  (AlgebraicGeometry.GenericScaling.stabilizerDimension :
    topologicalKrullDim
      AlgebraicGeometry.GenericScaling.groupoid.stabilizer.X.left.left = 0)

/- Remark 40.10.11 (6): The arrow scheme and stabilizer have unequal topological Krull
dimensions. -/
@[stacks 04MR] #check
  (AlgebraicGeometry.GenericScaling.dimensionEqualityFails :
    topologicalKrullDim AlgebraicGeometry.GenericScaling.groupoid.R.left ≠
      topologicalKrullDim
        AlgebraicGeometry.GenericScaling.groupoid.stabilizer.X.left.left)

/- Remark 40.10.11 (7): The source and target maps are not both locally of finite type. -/
@[stacks 04MR] #check
  (AlgebraicGeometry.GenericScaling.not_bothLocallyOfFiniteType :
    ¬ (AlgebraicGeometry.LocallyOfFiniteType
          AlgebraicGeometry.GenericScaling.groupoid.s.left ∧
        AlgebraicGeometry.LocallyOfFiniteType
          AlgebraicGeometry.GenericScaling.groupoid.t.left))
