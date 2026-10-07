module

import StacksCheckRecall
public import stacks_project.Chap55.Definition_55_8_4_MinimalModel
public import stacks_project.Chap55.Lemma_55_8_5_Model

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Proposition 55.8.6: For a smooth projective curve `C` over the fraction field `K`
of a discrete valuation ring `R` with `H⁰(C, 𝒪_C) = K`, a minimal regular model exists. -/
@[stacks 0C2W]
theorem exists_minimalModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    ∃ M : RegularModel R K C, IsMinimalModel M.base := sorry

end AlgebraicGeometry.Scheme.Hom
