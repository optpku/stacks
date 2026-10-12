/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
public import ReasLib.RingTheory.Module.Support.Minimal
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Localization of two-periodic complexes

This file constructs the localization of a two-periodic endomorphism complex at a prime and
records its behavior at a minimal point of the support.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R]

/-- The two localized differentials still compose to zero in degree zero. -/
theorem localizedAtPrime_d₀_d₁
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₀.hom) ≫
      ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₁.hom) = 0 := sorry

/-- The two localized differentials still compose to zero in degree one. -/
theorem localizedAtPrime_d₁_d₀
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₁.hom) ≫
      ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₀.hom) = 0 := sorry

/-- The two-periodic endomorphism complex obtained by localizing its module and differentials at
a prime ideal. -/
noncomputable def localizedAtPrime
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    TwoPeriodicEndomorphism (ModuleCat.{max u v} (Localization.AtPrime q.asIdeal)) where
  X := ModuleCat.of (Localization.AtPrime q.asIdeal)
    (LocalizedModule.AtPrime q.asIdeal K.X)
  d₀ := ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₀.hom)
  d₁ := ModuleCat.ofHom (LocalizedModule.map q.asIdeal.primeCompl K.d₁.hom)
  d₀_d₁ := localizedAtPrime_d₀_d₁ K q
  d₁_d₀ := localizedAtPrime_d₁_d₀ K q

/-- The carrier of `localizedAtPrime K q` is the localization of `K.X` at `q`. -/
theorem localizedAtPrime_X
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    (localizedAtPrime K q).X = ModuleCat.of (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal K.X) := sorry

/-- The degree-zero differential of `localizedAtPrime K q` is the localized map of `K.d₀`. -/
theorem localizedAtPrime_d₀
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    (localizedAtPrime K q).d₀.hom =
      LocalizedModule.map q.asIdeal.primeCompl K.d₀.hom := sorry

/-- The degree-one differential of `localizedAtPrime K q` is the localized map of `K.d₁`. -/
theorem localizedAtPrime_d₁
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (q : PrimeSpectrum R) :
    (localizedAtPrime K q).d₁.hom =
      LocalizedModule.map q.asIdeal.primeCompl K.d₁.hom := sorry

variable [IsLocalRing R] [IsNoetherianRing R]

/-- Localization at a minimal point of the support of a finite module has finite length over the
local ring at that point. -/
theorem localizedAtPrime_isFiniteLength
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (q : PrimeSpectrum R) (hq : Minimal (· ∈ Module.support R K.X) q) :
    IsFiniteLength (Localization.AtPrime q.asIdeal) (localizedAtPrime K q).X := sorry

/-- If both cohomology modules have finite length and the support has dimension one, then the
localized two-periodic complex is acyclic at every minimal support point. -/
theorem localizedAtPrime_acyclic
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) [Module.Finite R K.X]
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
    (hdim : Module.supportDim R K.X = 1) (q : PrimeSpectrum R)
    (hq : Minimal (· ∈ Module.support R K.X) q) :
    (localizedAtPrime K q).toCochainComplex.Acyclic := sorry

end CategoryTheory.TwoPeriodicEndomorphism
