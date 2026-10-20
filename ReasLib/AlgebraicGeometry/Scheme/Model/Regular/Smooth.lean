module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Existence

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A smooth projective curve over the fraction field of a discrete valuation ring,
whose global functions are precisely the constants, has a smooth regular model if and
only if it has a smooth minimal regular model. -/
theorem exists_smoothModel_iff_exists_smoothMinimalModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    (∃ M : RegularModel R K C, Smooth M.base) ↔
      ∃ M : RegularModel R K C, IsMinimalModel M.base ∧ Smooth M.base := sorry

/-- A smooth projective curve over the fraction field of a discrete valuation ring,
whose global functions are precisely the constants, has a smooth minimal regular model
if and only if every minimal regular model is smooth. -/
theorem exists_smoothMinimalModel_iff_forall_minimalModel_smooth
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    (∃ M : RegularModel R K C, IsMinimalModel M.base ∧ Smooth M.base) ↔
      ∀ M : RegularModel R K C, IsMinimalModel M.base → Smooth M.base := sorry

end AlgebraicGeometry.Scheme.Hom
