/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MinimalModel
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A smooth projective curve over the fraction field of a discrete valuation ring,
whose global functions are precisely the constants, admits a minimal regular model. -/
theorem exists_minimalModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    ∃ M : RegularModel R K C, IsMinimalModel M.base := sorry

end AlgebraicGeometry.Scheme.Hom
