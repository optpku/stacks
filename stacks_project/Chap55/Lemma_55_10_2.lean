module

import StacksCheckRecall
public import stacks_project.Chap55.Lemma_55_10_1
public import stacks_project.Chap55.Lemma_55_10_2_ModelMorphism
public import stacks_project.Chap55.Lemma_55_10_2_ContractionSequence

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Lemma 55.10.2 (1): A positive-genus smooth projective curve with only constant global
functions has a unique morphism from any regular proper model to a fixed minimal model. -/
@[stacks 0C9Z]
theorem existsUnique_modelMorphism_to_minimalModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : 0 < SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections)
    (X Y : RegularModel R K C) [IsMinimalModel X.base] :
    ∃! f : Over.mk Y.base ⟶ Over.mk X.base, IsModelMorphism Y X f := sorry

/-- Lemma 55.10.2 (2): Every morphism from a regular proper model to the fixed minimal model
is represented by a finite sequence of contractions of exceptional curves of the first kind. -/
@[stacks 0C9Z]
theorem modelMorphism_to_minimalModel_isContractionSequence
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : 0 < SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections)
    (X Y : RegularModel R K C) [IsMinimalModel X.base]
    (f : Over.mk Y.base ⟶ Over.mk X.base) (hf : IsModelMorphism Y X f) :
    IsContractionSequence Y X f := sorry

end AlgebraicGeometry.Scheme.Hom
