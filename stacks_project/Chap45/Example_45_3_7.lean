/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Correspondence.ProjectiveLine

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence.ProjectiveLine

variable {k : Type u} [Field k]

#check (toCohomology k : End k ≃ₗ[ℚ] Cohomology k)

#check (poincareDuality k : Cohomology k ≃ₗ[ℚ] Homology k)

#check (one_eq_diagonal : (1 : End k) = diagonal k)

#check (diagonal_eq_add :
  (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) →
    diagonal k = pointTimes x + timesPoint x)

#check (pointTimes_mul_pointTimes :
  (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) →
    pointTimes x * pointTimes x = pointTimes x)

#check (pointTimes_mul_timesPoint :
  (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) →
    pointTimes x * timesPoint x = 0)

#check (timesPoint_mul_pointTimes :
  (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) →
    timesPoint x * pointTimes x = 0)

#check (timesPoint_mul_timesPoint :
  (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) →
    timesPoint x * timesPoint x = timesPoint x)

/- Example 45.3.7: for a chosen rational point of `ℙ¹_k`, the two point
correspondences coordinatize its degree-zero rational correspondence algebra. -/
@[stacks 0FG6] #check (AlgebraicGeometry.Correspondence.ProjectiveLine.fromProd_bijective :
  (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) →
    Function.Bijective (fromProd x))

end AlgebraicGeometry.Correspondence.ProjectiveLine
