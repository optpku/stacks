/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Domination

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.10.2 -/
@[stacks 0C9Z] #check
  (AlgebraicGeometry.Scheme.Hom.existsUnique_modelMorphism_to_minimalModel :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : 0 < SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections)
    (X Y : RegularModel R K C) [IsMinimalModel X.base],
    ∃ f : Over.mk Y.base ⟶ Over.mk X.base,
      IsModelMorphism Y X f ∧ IsContractionSequence Y X f ∧
        ∀ g : Over.mk Y.base ⟶ Over.mk X.base, IsModelMorphism Y X g → g = f)

/- Lemma 55.10.2 (2) -/
@[stacks 0C9Z] #check
  (AlgebraicGeometry.Scheme.Hom.modelMorphism_to_minimalModel_isContractionSequence :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : 0 < SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections)
    (X Y : RegularModel R K C) [IsMinimalModel X.base]
    (f : Over.mk Y.base ⟶ Over.mk X.base) (hf : IsModelMorphism Y X f),
    IsContractionSequence Y X f)

end AlgebraicGeometry.Scheme.Hom
