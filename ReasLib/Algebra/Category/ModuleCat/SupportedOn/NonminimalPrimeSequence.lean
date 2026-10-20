/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.NonminimalPrimes
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.PointTerms

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped ZeroObject

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A]

/-- For a Noetherian specialization-stable subset, local cohomology admits the
exact sequence from the support-pair colimit through nonminimal and total support
to the coproduct of localized cohomology at minimal points, with the canonical
support-inclusion map as its middle arrow. -/
theorem existsNonminimalPrimesExactSequence [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (M : ModuleCat.{u} A) (i : ℤ) :
    ∃ a : colimit (principalFirstCohomologyDiagram T (nonminimalPrimes T) M i) ⟶
        cohomology (nonminimalPrimes T) (ModuleCat.single0 M) i,
      ∃ c : cohomology T (ModuleCat.single0 M) i ⟶
          minimalPointLocalCohomologySum T M i,
        (ComposableArrows.mk₄
          (0 : (0 : ModuleCat.{u} A) ⟶
            colimit (principalFirstCohomologyDiagram T (nonminimalPrimes T) M i))
          a (supportCohomologyMap (nonminimalPrimes_subset T) (ModuleCat.single0 M) i) c).Exact := sorry

end CategoryTheory.ModuleCat.SupportedOn
