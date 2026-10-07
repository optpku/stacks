module

import StacksCheckRecall
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap53.Lemma_53_20_12_Nodal
public import stacks_project.Chap55.Lemma_55_10_1
public import stacks_project.Chap55.Lemma_55_12_4
public import stacks_project.Chap55.Proposition_55_8_6

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Lemma 55.14.5: for a smooth projective curve `C` over the fraction field `K` of a
discrete valuation ring `R`, with `H⁰(C, 𝒪_C) = K`, the following are equivalent:
there is a proper at-worst-nodal model, there is a minimal at-worst-nodal model, and every
minimal model is at worst nodal. -/
@[stacks 0CDG]
theorem atWorstNodalModel_tfae
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    let hasAtWorstNodalModel :=
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
        (genericFiberIso : C ≅ Over.mk
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
        Flat f ∧ FiniteType f ∧ IsProper f ∧ AtWorstNodal f
    let hasMinimalAtWorstNodalModel :=
      ∃ M : RegularModel R K C, IsMinimalModel M.base ∧ AtWorstNodal M.base
    let everyMinimalModelAtWorstNodal :=
      ∀ M : RegularModel R K C, IsMinimalModel M.base → AtWorstNodal M.base
    List.TFAE [hasAtWorstNodalModel, hasMinimalAtWorstNodalModel,
      everyMinimalModelAtWorstNodal] := sorry

/-- Existence of a proper at-worst-nodal model is equivalent to existence of a minimal
at-worst-nodal regular model. -/
theorem existsAtWorstNodalModel_iff_existsMinimal
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    (∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
      Flat f ∧ FiniteType f ∧ IsProper f ∧ AtWorstNodal f) ↔
        ∃ M : RegularModel R K C, IsMinimalModel M.base ∧ AtWorstNodal M.base := sorry

/-- Existence of a minimal at-worst-nodal model is equivalent to at-worst-nodality of
every minimal model. -/
theorem existsMinimalAtWorstNodal_iff_forallMinimal
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    (∃ M : RegularModel R K C, IsMinimalModel M.base ∧ AtWorstNodal M.base) ↔
      ∀ M : RegularModel R K C, IsMinimalModel M.base → AtWorstNodal M.base := sorry

end AlgebraicGeometry.Scheme.Hom
