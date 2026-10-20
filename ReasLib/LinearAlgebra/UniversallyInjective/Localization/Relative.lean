/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.RingTheory.Localization.Module
public import ReasLib.LinearAlgebra.UniversallyInjective
public import ReasLib.RingTheory.Localization.AtPrime.Map
public import ReasLib.RingTheory.Localization.Away.Relative

/-!
# Universally injective maps over a localization

This file contains base-change comparisons for tensor-stable injectivity over localizations and
predicates for principal localization along a base ring and localization at a base prime.

@stack 05CL
-/

@[expose] public section

universe u v w x z

variable {R : Type u} [CommRing R]

namespace LinearMap.UniversallyInjective

variable {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {M' : Type x} [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']

/-- Universal injectivity of an `A`-linear map viewed over the base ring `R`.

The restricted module and scalar-tower structures are canonical once the algebra `R → A` is
fixed, but are kept inside this predicate so callers do not have to rebuild them locally. -/
@[stacks 05CL "universal injectivity over a base ring"]
def overBase (f : M →ₗ[A] M') : Prop :=
  -- Local instance justification (instance diamond): restriction structures are canonical for
  -- this selected algebra, but registering them globally would create competing scalar towers.
  letI : Module R M := Module.restrictScalars R A M
  letI : Module R M' := Module.restrictScalars R A M'
  letI : IsScalarTower R A M := IsScalarTower.restrictScalars R A M
  letI : IsScalarTower R A M' := IsScalarTower.restrictScalars R A M'
  LinearMap.UniversallyInjective.{u, w, x, z} (f.restrictScalars R)

end LinearMap.UniversallyInjective

namespace LinearMap.UniversallyInjective.Localization

variable {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {M' : Type x} [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']

/-- Tensor-stable injectivity of a map of modules over a localization is equivalent whether the
map is viewed over the original ring or over the localized ring. -/
@[stacks 05CL "universal injectivity under localization"]
theorem restrictScalars_iff_of_isLocalization
    {T : Submonoid R} [IsLocalization T A] (f : M →ₗ[A] M') :
    UniversallyInjective.{u, w, x, z} (f.restrictScalars R) ↔
      UniversallyInjective.{v, w, x, z} f := sorry

end LinearMap.UniversallyInjective.Localization

namespace LinearMap.UniversallyInjective

variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]
variable {N : Type x} [AddCommGroup N] [Module S N]

/-- Universal injectivity over `Localization.Away f` of the principal localization of an
`S`-linear map away from the image of `f : R`. -/
noncomputable def awayOverBase (phi : M →ₗ[S] N) (f : R) : Prop :=
  -- Local instance justification (instance diamond): selected `R → S` relative algebra action.
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    Localization.Away.Relative.algebraMapAlgebra f
  -- Local instance justification (instance diamond): source action induced by the selected relative algebra action.
  letI : Module (Localization.Away f)
      (LocalizedModule.Away (algebraMap R S f) M) :=
    Localization.Away.Relative.algebraMapModule f
  -- Local instance justification (instance diamond): target action induced by the selected relative algebra action.
  letI : Module (Localization.Away f)
      (LocalizedModule.Away (algebraMap R S f) N) :=
    Localization.Away.Relative.algebraMapModule f
  -- Local instance justification (instance diamond): source tower for the selected relative localization action.
  letI : IsScalarTower (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
    Localization.Away.Relative.mapModule_isScalarTower (algebraMap R S) f
  -- Local instance justification (instance diamond): target tower for the selected relative localization action.
  letI : IsScalarTower (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) N) :=
    Localization.Away.Relative.mapModule_isScalarTower (algebraMap R S) f
  LinearMap.UniversallyInjective.{u, max v w, max v x, z}
    ((LocalizedModule.map (Submonoid.powers (algebraMap R S f)) phi).restrictScalars
      (Localization.Away f))

/-- `awayOverBase phi f` is universal injectivity of the canonical localized map with respect to
the relative `Localization.Away f`-action induced by `R → S`. -/
theorem awayOverBase_iff (phi : M →ₗ[S] N) (f : R) :
    awayOverBase.{u, v, w, x, z} phi f ↔
      (
       -- Local instance justification (instance diamond): relative algebra action selected by `awayOverBase`.
       letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
          Localization.Away.Relative.algebraMapAlgebra f
       -- Local instance justification (instance diamond): source-module action selected by `awayOverBase`.
       letI : Module (Localization.Away f)
            (LocalizedModule.Away (algebraMap R S f) M) :=
          Localization.Away.Relative.algebraMapModule f
       -- Local instance justification (instance diamond): target-module action selected by `awayOverBase`.
       letI : Module (Localization.Away f)
            (LocalizedModule.Away (algebraMap R S f) N) :=
          Localization.Away.Relative.algebraMapModule f
       -- Local instance justification (instance diamond): source tower used by `awayOverBase`.
       letI : IsScalarTower (Localization.Away f) (Localization.Away (algebraMap R S f))
            (LocalizedModule.Away (algebraMap R S f) M) :=
          Localization.Away.Relative.mapModule_isScalarTower (algebraMap R S) f
       -- Local instance justification (instance diamond): target tower used by `awayOverBase`.
       letI : IsScalarTower (Localization.Away f) (Localization.Away (algebraMap R S f))
            (LocalizedModule.Away (algebraMap R S f) N) :=
          Localization.Away.Relative.mapModule_isScalarTower (algebraMap R S) f
       LinearMap.UniversallyInjective.{u, max v w, max v x, z}
          ((LocalizedModule.map (Submonoid.powers (algebraMap R S f)) phi).restrictScalars
            (Localization.Away f)))
    := sorry

/-- Universal injectivity over `Localization.AtPrime p.asIdeal` of the localization of an
`S`-linear map at the image of the prime-complement submonoid of `p`. -/
noncomputable def atBasePrime (phi : M →ₗ[S] N) (p : PrimeSpectrum R) : Prop :=
  let T := Submonoid.map (algebraMap R S) p.asIdeal.primeCompl
  -- Local instance justification (instance diamond): algebra action selected by the base map and prime.
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization T) :=
    (Localization.AtPrime.map (algebraMap R S) p.asIdeal).toAlgebra
  -- Local instance justification (instance diamond): source action restricted along the base-prime map.
  letI : Module (Localization.AtPrime p.asIdeal) (LocalizedModule T M) :=
    Module.restrictScalars (Localization.AtPrime p.asIdeal) (Localization T)
      (LocalizedModule T M)
  -- Local instance justification (instance diamond): target action restricted along the base-prime map.
  letI : Module (Localization.AtPrime p.asIdeal) (LocalizedModule T N) :=
    Module.restrictScalars (Localization.AtPrime p.asIdeal) (Localization T)
      (LocalizedModule T N)
  -- Local instance justification (instance diamond): source tower induced by the base-prime map.
  letI : IsScalarTower (Localization.AtPrime p.asIdeal) (Localization T)
      (LocalizedModule T M) :=
    IsScalarTower.restrictScalars (Localization.AtPrime p.asIdeal) (Localization T)
      (LocalizedModule T M)
  -- Local instance justification (instance diamond): target tower induced by the base-prime map.
  letI : IsScalarTower (Localization.AtPrime p.asIdeal) (Localization T)
      (LocalizedModule T N) :=
    IsScalarTower.restrictScalars (Localization.AtPrime p.asIdeal) (Localization T)
      (LocalizedModule T N)
  LinearMap.UniversallyInjective.{u, max v w, max v x, z}
    ((LocalizedModule.map T phi).restrictScalars (Localization.AtPrime p.asIdeal))

/-- `atBasePrime phi p` is universal injectivity of the canonical map localized at the image of
`p.asIdeal.primeCompl`, viewed over the local base ring at `p`. -/
theorem atBasePrime_iff (phi : M →ₗ[S] N) (p : PrimeSpectrum R) :
    atBasePrime.{u, v, w, x, z} phi p ↔
      (let T := Submonoid.map (algebraMap R S) p.asIdeal.primeCompl
       -- Local instance justification (instance diamond): relative algebra action selected by `atBasePrime`.
       letI : Algebra (Localization.AtPrime p.asIdeal) (Localization T) :=
          (Localization.AtPrime.map (algebraMap R S) p.asIdeal).toAlgebra
       -- Local instance justification (instance diamond): source action selected by `atBasePrime`.
       letI : Module (Localization.AtPrime p.asIdeal) (LocalizedModule T M) :=
          Module.restrictScalars (Localization.AtPrime p.asIdeal) (Localization T)
            (LocalizedModule T M)
       -- Local instance justification (instance diamond): target action selected by `atBasePrime`.
       letI : Module (Localization.AtPrime p.asIdeal) (LocalizedModule T N) :=
          Module.restrictScalars (Localization.AtPrime p.asIdeal) (Localization T)
            (LocalizedModule T N)
       -- Local instance justification (instance diamond): source tower induced by the base-prime map.
       letI : IsScalarTower (Localization.AtPrime p.asIdeal) (Localization T)
            (LocalizedModule T M) :=
          IsScalarTower.restrictScalars (Localization.AtPrime p.asIdeal) (Localization T)
            (LocalizedModule T M)
       -- Local instance justification (instance diamond): target tower induced by the base-prime map.
       letI : IsScalarTower (Localization.AtPrime p.asIdeal) (Localization T)
            (LocalizedModule T N) :=
          IsScalarTower.restrictScalars (Localization.AtPrime p.asIdeal) (Localization T)
            (LocalizedModule T N)
       LinearMap.UniversallyInjective.{u, max v w, max v x, z}
          ((LocalizedModule.map T phi).restrictScalars (Localization.AtPrime p.asIdeal)))
    := sorry

end LinearMap.UniversallyInjective
