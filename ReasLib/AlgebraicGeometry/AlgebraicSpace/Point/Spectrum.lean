/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison

/-!
# The generic point of a domain spectrum as an algebraic space
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The unique generic point of `specSpace A`, as the image of the generic
point of `Spec (.of A)` under `ofOver.pointsEquiv`. -/
noncomputable def specSpaceGenericPoint (A : Type u) [CommRing A] [IsDomain A] :
    Points (specSpace A) :=
  ofOver.pointsEquiv (Over.mk (𝟙 (Spec (.of A)))) (genericPoint (Spec (.of A)))

/-- `specSpaceGenericPoint A` is `ofOver.pointsEquiv` of the generic point of
`Spec (.of A)`. -/
theorem specSpaceGenericPoint_eq (A : Type u) [CommRing A] [IsDomain A] :
    specSpaceGenericPoint A =
      ofOver.pointsEquiv (Over.mk (𝟙 (Spec (.of A))))
        (genericPoint (Spec (.of A))) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
