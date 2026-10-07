module

public import stacks_project.Chap55.Lemma_55_14_7

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

/-- Good reduction is equivalent to the existence of a smooth regular model. -/
theorem hasGoodReduction_iff_exists_smoothModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] :
    hasGoodReduction R K C ↔ ∃ M : RegularModel R K C, Smooth M.base := sorry

/-- Under the global-sections hypothesis, good reduction is equivalent to the existence
of a smooth minimal regular model. -/
theorem hasGoodReduction_iff_exists_smoothMinimalModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    hasGoodReduction R K C ↔
      ∃ M : RegularModel R K C, IsMinimalModel M.base ∧ Smooth M.base := sorry

/-- Under the global-sections hypothesis, good reduction is equivalent to smoothness of
every minimal regular model. -/
theorem hasGoodReduction_iff_forall_minimalModel_smooth
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    hasGoodReduction R K C ↔
      ∀ M : RegularModel R K C, IsMinimalModel M.base → Smooth M.base := sorry

end AlgebraicGeometry.Scheme.Hom
