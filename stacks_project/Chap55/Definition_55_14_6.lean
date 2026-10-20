/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.Characterization

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Definition 55.14.6: a smooth projective curve `C` over the fraction field `K` of a
discrete valuation ring `R`, with `H⁰(C, 𝒪_C) = K`, has semistable reduction exactly
when it admits a proper flat finite-type model that is at worst nodal. -/
@[stacks 0CDH] #check (AlgebraicGeometry.Scheme.Hom.hasSemistableReduction_iff_existsAtWorstNodalModel :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
    hasSemistableReduction R K C ↔
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
        (genericFiberIso : C ≅ Over.mk
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
        Flat f ∧ FiniteType f ∧ IsProper f ∧ AtWorstNodal f)

end AlgebraicGeometry.Scheme.Hom
