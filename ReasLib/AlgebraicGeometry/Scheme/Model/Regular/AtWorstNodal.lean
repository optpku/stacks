/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MinimalModel
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a smooth projective curve `C` over the fraction field `K` of a
discrete valuation ring `R`, with `H⁰(C, 𝒪_C) = K`, the following are equivalent:
there is a proper at-worst-nodal model, there is a minimal at-worst-nodal model, and every
minimal model is at worst nodal. -/
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
        ∃ M : RegularModel R K C, IsMinimalModel M.base ∧ AtWorstNodal M.base :=
  (atWorstNodalModel_tfae R K C h_globalSections).out 0 1

/-- Existence of a minimal at-worst-nodal model is equivalent to at-worst-nodality of
every minimal model. -/
theorem existsMinimalAtWorstNodal_iff_forallMinimal
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    (∃ M : RegularModel R K C, IsMinimalModel M.base ∧ AtWorstNodal M.base) ↔
      ∀ M : RegularModel R K C, IsMinimalModel M.base → AtWorstNodal M.base :=
  (atWorstNodalModel_tfae R K C h_globalSections).out 1 2

end AlgebraicGeometry.Scheme.Hom
