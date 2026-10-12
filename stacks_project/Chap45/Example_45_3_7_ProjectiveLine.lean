/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.ProjectiveLine

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence.ProjectiveLine

#check (Product : (k : Type u) → [Field k] → SchemeOverField k)

#check (End : (k : Type u) → [Field k] → Type (u + 1))

#check (lineDimension : (k : Type u) → [Field k] →
  topologicalKrullDim (ProjectiveSpace.schemeOver k 1).left = (1 : WithBot ℕ∞))

#check (toHomology : (k : Type u) → [Field k] → End k ≃ₗ[ℚ] Homology k)

#check (toCohomology : (k : Type u) → [Field k] → End k ≃ₗ[ℚ] Cohomology k)

#check (pointTimes : {k : Type u} → [Field k] →
  (SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) → End k)

#check (timesPoint : {k : Type u} → [Field k] →
  (SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) → End k)

#check (fromProd_bijective : {k : Type u} → [Field k] →
  (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) →
    Function.Bijective (fromProd x))

end AlgebraicGeometry.Correspondence.ProjectiveLine
