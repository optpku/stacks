/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.NonminimalPrimes
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.PointTerms
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.NonminimalPrimeSequence

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open scoped ZeroObject

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A]

/- Lemma 51.6.1 (1): if `T ⊆ Spec(A)` is stable under specialization, then its
subset of nonminimal primes is stable under specialization. -/
@[stacks 0EF8] #check (CategoryTheory.ModuleCat.SupportedOn.nonminimalPrimes_stable :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T),
    StableUnderSpecialization (CategoryTheory.ModuleCat.SupportedOn.nonminimalPrimes T))

/- Lemma 51.6.1 (2): for every `A`-module `M`, there are arrows making the source's
sequence from `colim_(Z,f) H¹_f(H_Z^(i-1)(M))` through `H^i_(nonminimalPrimes T)(M)`
and `H^i_T(M)` to `⨁ p, H^i_(p A_p)(M_p)` exact at its three internal terms,
with the canonical support-inclusion map as the middle arrow. -/
@[stacks 0EF8] #check (CategoryTheory.ModuleCat.SupportedOn.existsNonminimalPrimesExactSequence :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (M : ModuleCat.{u} A) (i : ℤ),
    ∃ a : colimit
        (CategoryTheory.ModuleCat.SupportedOn.principalFirstCohomologyDiagram
          T (CategoryTheory.ModuleCat.SupportedOn.nonminimalPrimes T) M i) ⟶
        cohomology (CategoryTheory.ModuleCat.SupportedOn.nonminimalPrimes T)
          (ModuleCat.single0 M) i,
      ∃ c : cohomology T (ModuleCat.single0 M) i ⟶
          CategoryTheory.ModuleCat.SupportedOn.minimalPointLocalCohomologySum T M i,
        (ComposableArrows.mk₄
          (0 : (0 : ModuleCat.{u} A) ⟶
            colimit
              (CategoryTheory.ModuleCat.SupportedOn.principalFirstCohomologyDiagram
                T (CategoryTheory.ModuleCat.SupportedOn.nonminimalPrimes T) M i))
          a (supportCohomologyMap (nonminimalPrimes_subset T) (ModuleCat.single0 M) i) c).Exact)

end CategoryTheory.ModuleCat.SupportedOn
