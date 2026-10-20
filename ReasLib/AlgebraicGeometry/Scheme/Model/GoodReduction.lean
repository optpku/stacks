/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Basic

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A smooth projective curve over the fraction field of a discrete valuation ring has
good reduction when it admits a smooth regular model over that ring. -/
def hasGoodReduction (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] : Prop :=
  ∃ M : RegularModel R K C, Smooth M.base

/-- Good reduction is exactly the existence of a smooth regular model. -/
theorem hasGoodReduction_iff_exists_smoothModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] :
    hasGoodReduction R K C ↔ ∃ M : RegularModel R K C, Smooth M.base :=
  Iff.rfl

end AlgebraicGeometry.Scheme.Hom
