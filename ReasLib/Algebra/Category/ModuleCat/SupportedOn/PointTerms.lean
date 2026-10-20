/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.NonminimalPrimes

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A]

/-- The extension `p A_p` of a prime ideal `p` to its local ring. -/
def extendedPrime (p : PrimeSpectrum A) : Ideal (Localization.AtPrime p.asIdeal) :=
  p.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))

/-- The local cohomology module `H^i_(p A_p)(M_p)` over `A_p`. -/
noncomputable def localCohomologyAtPrime (M : ModuleCat.{u} A) (i : ℤ)
    (p : PrimeSpectrum A) : ModuleCat.{u} (Localization.AtPrime p.asIdeal) :=
  cohomology (PrimeSpectrum.zeroLocus (extendedPrime p))
    (ModuleCat.single0
      (ModuleCat.of (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M))) i

/-- The local cohomology module `H^i_(p A_p)(M_p)`, regarded as an `A`-module. -/
noncomputable def restrictedLocalCohomologyAtPrime (M : ModuleCat.{u} A) (i : ℤ)
    (p : PrimeSpectrum A) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime p.asIdeal))).obj
    (localCohomologyAtPrime M i p)

/-- The restricted point term is local cohomology over `A_p`, viewed as an `A`-module. -/
theorem restrictedLocalCohomologyAtPrime_def (M : ModuleCat.{u} A) (i : ℤ)
    (p : PrimeSpectrum A) :
    restrictedLocalCohomologyAtPrime M i p =
      (ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime p.asIdeal))).obj
        (localCohomologyAtPrime M i p) := sorry

/-- The full subcategory of primes lying in `T \ nonminimalPrimes T`. -/
abbrev MinimalPoints (T : Set (PrimeSpectrum A)) :=
  ObjectProperty.FullSubcategory (fun p : PrimeSpectrum A ↦ p ∈ T \ nonminimalPrimes T)

/-- A prime is a minimal point of `T` exactly when it lies in `T` but not in
`nonminimalPrimes T`. -/
theorem mem_minimalPoints_iff {T : Set (PrimeSpectrum A)} (p : PrimeSpectrum A) :
    p ∈ T \ nonminimalPrimes T ↔ p ∈ T ∧ p ∉ nonminimalPrimes T := sorry

/-- The direct sum of localized local-cohomology modules over the minimal points of `T`. -/
noncomputable def minimalPointLocalCohomologySum (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{u} A) (i : ℤ) : ModuleCat.{u} A :=
  ∐ fun p : MinimalPoints T ↦ restrictedLocalCohomologyAtPrime M i p.obj

/-- The minimal-point endpoint is the coproduct of the restricted localized
local-cohomology modules. -/
theorem minimalPointLocalCohomologySum_def (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{u} A) (i : ℤ) :
    minimalPointLocalCohomologySum T M i =
      ∐ fun p : MinimalPoints T ↦ restrictedLocalCohomologyAtPrime M i p.obj := sorry

end CategoryTheory.ModuleCat.SupportedOn
