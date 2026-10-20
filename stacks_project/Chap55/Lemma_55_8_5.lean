/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Contraction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.8.5: For a smooth projective curve `C` over the fraction field `K` of a
discrete valuation ring `R` with `H⁰(C, 𝒪_C) = K`, every regular proper model admits a finite
sequence of contractions of exceptional curves of the first kind ending in a minimal model. -/
@[stacks 0CD9]
#check (AlgebraicGeometry.Scheme.Hom.exists_contractionSequence :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (M : RegularModel R K C),
    ∃ m : ℕ, ∃ models : Fin (m + 1) → RegularModel R K C,
      models (Fin.last m) = M ∧
        ∃ contractions : ∀ i : Fin m, ContractionStep (models i.succ) (models i.castSucc),
          IsMinimalModel (models 0).base)

end AlgebraicGeometry.Scheme.Hom
