/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Existence

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Proposition 55.8.6: For a smooth projective curve `C` over the fraction field `K`
of a discrete valuation ring `R` with `H⁰(C, 𝒪_C) = K`, a minimal regular model exists. -/
@[stacks 0C2W] #check (AlgebraicGeometry.Scheme.Hom.exists_minimalModel :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
    ∃ M : RegularModel R K C, IsMinimalModel M.base)

end AlgebraicGeometry.Scheme.Hom
