/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap55.Definition_55_8_4_MinimalModel
public import stacks_project.Chap55.Lemma_55_8_5_Model
public import stacks_project.Chap55.Lemma_55_8_5_Contraction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Lemma 55.8.5: For a smooth projective curve `C` over the fraction field `K` of a
discrete valuation ring `R` with `H⁰(C, 𝒪_C) = K`, every regular proper model admits a finite
sequence of contractions of exceptional curves of the first kind ending in a minimal model. -/
@[stacks 0CD9]
theorem exists_contractionSequence
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (M : RegularModel R K C) :
    ∃ m : ℕ, ∃ models : Fin (m + 1) → RegularModel R K C,
      models (Fin.last m) = M ∧
        ∃ contractions : ∀ i : Fin m, ContractionStep (models i.succ) (models i.castSucc),
          IsMinimalModel (models 0).base := sorry

end AlgebraicGeometry.Scheme.Hom
