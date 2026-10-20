module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Smooth

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.14.7 (1): A smooth projective curve over the fraction field of a discrete
valuation ring has a proper smooth model if and only if it has a smooth minimal model. -/
@[stacks 0CDI]
#check (AlgebraicGeometry.Scheme.Hom.exists_smoothModel_iff_exists_smoothMinimalModel :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
    (∃ M : RegularModel R K C, Smooth M.base) ↔
      ∃ M : RegularModel R K C, IsMinimalModel M.base ∧ Smooth M.base)

/- Lemma 55.14.7 (2): A smooth projective curve over the fraction field of a discrete
valuation ring has a smooth minimal model if and only if every minimal model is smooth. -/
@[stacks 0CDI]
#check (AlgebraicGeometry.Scheme.Hom.exists_smoothMinimalModel_iff_forall_minimalModel_smooth :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
    (∃ M : RegularModel R K C, IsMinimalModel M.base ∧ Smooth M.base) ↔
      ∀ M : RegularModel R K C, IsMinimalModel M.base → Smooth M.base)

end AlgebraicGeometry.Scheme.Hom
