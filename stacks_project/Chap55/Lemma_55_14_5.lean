/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.AtWorstNodal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.14.5: for a smooth projective curve over the fraction field of a discrete
valuation ring with only constant global functions, existence of a proper at-worst-nodal
model, existence of a minimal at-worst-nodal model, and at-worst-nodality of every minimal
model are equivalent. -/
@[stacks 0CDG] #check (AlgebraicGeometry.Scheme.Hom.atWorstNodalModel_tfae :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
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
      everyMinimalModelAtWorstNodal])

#check (AlgebraicGeometry.Scheme.Hom.existsAtWorstNodalModel_iff_existsMinimal :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
    (∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
      Flat f ∧ FiniteType f ∧ IsProper f ∧ AtWorstNodal f) ↔
        ∃ M : RegularModel R K C, IsMinimalModel M.base ∧ AtWorstNodal M.base)

#check (AlgebraicGeometry.Scheme.Hom.existsMinimalAtWorstNodal_iff_forallMinimal :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
    (∃ M : RegularModel R K C, IsMinimalModel M.base ∧ AtWorstNodal M.base) ↔
      ∀ M : RegularModel R K C, IsMinimalModel M.base → AtWorstNodal M.base)

end AlgebraicGeometry.Scheme.Hom
