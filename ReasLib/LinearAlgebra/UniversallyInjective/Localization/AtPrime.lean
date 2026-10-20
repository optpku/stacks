module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.TFAE
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import ReasLib.LinearAlgebra.UniversallyInjective.Localization.Relative
public import ReasLib.RingTheory.Localization.AtPrime.Relative

/-!
# Prime-local criteria for universally injective linear maps

The predicates in this file package the scalar actions used to regard an
`S`-linear map over a base ring `R` and its localizations.  Relative local
actions stay inside the relevant predicate and are never registered as
instances.

@stack 05CL
-/

@[expose] public section

universe u v w x z

namespace LinearMap.UniversallyInjective

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]
variable {M' : Type x} [AddCommGroup M'] [Module S M']

/-- Universal injectivity over `R` of the localization of an `S`-linear map at a prime of `S`. -/
@[stacks 05CL "universal injectivity at a prime"]
noncomputable def atPrime (f : M →ₗ[S] M') (q : PrimeSpectrum S) : Prop :=
  -- Local instance justification (instance diamond): these are the canonical restrictions for
  -- the chosen base algebra, and must stay inside the prime-local predicate.
  letI : Module R M := Module.restrictScalars R S M
  letI : Module R M' := Module.restrictScalars R S M'
  letI : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
  letI : IsScalarTower R S M' := IsScalarTower.restrictScalars R S M'
  LinearMap.UniversallyInjective.{u, max v w, max v x, z}
    ((LocalizedModule.map q.asIdeal.primeCompl f).restrictScalars R)

/-- Universal injectivity over `R` of the localization of an `S`-linear map at a maximal ideal
of `S`. -/
@[stacks 05CL "universal injectivity at a maximal ideal"]
noncomputable def atMaximal (f : M →ₗ[S] M') (m : MaximalSpectrum S) : Prop :=
  atPrime.{u, v, w, x, z} (R := R) f m.toPrimeSpectrum

/-- Universal injectivity over `Localization.AtPrime (q.asIdeal.under R)` of the localization of
an `S`-linear map at a prime of `S`. -/
@[stacks 05CL "relative universal injectivity at a prime"]
noncomputable def atPrimeOver (f : M →ₗ[S] M') (q : PrimeSpectrum S) : Prop :=
  -- Local instance justification (instance diamond): the relative AtPrime module structures are
  -- selected by the contracted prime and are not globally coherent for arbitrary primes.
  letI : Module (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule.AtPrime q.asIdeal M) :=
    Localization.AtPrime.Relative.algebraMapModule (R := R) (M := M) q.asIdeal
  letI : Module (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule.AtPrime q.asIdeal M') :=
    Localization.AtPrime.Relative.algebraMapModule (R := R) (M := M') q.asIdeal
  LinearMap.UniversallyInjective.{u, max v w, max v x, z}
    (LocalizedModule.mapAtPrimeOver (R := R) q.asIdeal f)

/-- Universal injectivity over `Localization.AtPrime (m.asIdeal.under R)` of the localization of
an `S`-linear map at a maximal ideal of `S`. -/
@[stacks 05CL "relative universal injectivity at a maximal ideal"]
noncomputable def atMaximalOver (f : M →ₗ[S] M') (m : MaximalSpectrum S) : Prop :=
  atPrimeOver.{u, v, w, x, z} (R := R) f m.toPrimeSpectrum

/-- Universal injectivity over the base ring is detected after localization at every prime. -/
@[stacks 05CL "universal injectivity is local at primes"]
theorem iff_forall_atPrime (f : M →ₗ[S] M') :
    overBase.{u, v, w, x, z} (R := R) f ↔
      ∀ q : PrimeSpectrum S, atPrime.{u, v, w, x, z} (R := R) f q := sorry

/-- Universal injectivity over the base ring is detected after localization at every maximal
ideal. -/
@[stacks 05CL "universal injectivity is local at maximal ideals"]
theorem iff_forall_atMaximal (f : M →ₗ[S] M') :
    overBase.{u, v, w, x, z} (R := R) f ↔
      ∀ m : MaximalSpectrum S, atMaximal.{u, v, w, x, z} (R := R) f m := sorry

/-- Universal injectivity over the base ring is detected over the local base rings at all
contracted primes. -/
@[stacks 05CL "universal injectivity at contracted primes"]
theorem iff_forall_atPrimeOver (f : M →ₗ[S] M') :
    overBase.{u, v, w, x, z} (R := R) f ↔
      ∀ q : PrimeSpectrum S, atPrimeOver.{u, v, w, x, z} (R := R) f q := sorry

/-- Universal injectivity over the base ring is detected over the local base rings at all
contracted maximal ideals. -/
@[stacks 05CL "universal injectivity at contracted maximal ideals"]
theorem iff_forall_atMaximalOver (f : M →ₗ[S] M') :
    overBase.{u, v, w, x, z} (R := R) f ↔
      ∀ m : MaximalSpectrum S, atMaximalOver.{u, v, w, x, z} (R := R) f m := sorry

/-- Universal injectivity over `R` is equivalent to each prime-local and
maximal-local criterion, both over `R` and over the corresponding contracted local base rings. -/
@[stacks 05CL]
theorem tfae_local (f : M →ₗ[S] M') :
    List.TFAE [
      overBase.{u, v, w, x, z} (R := R) f,
      ∀ q : PrimeSpectrum S, atPrime.{u, v, w, x, z} (R := R) f q,
      ∀ m : MaximalSpectrum S, atMaximal.{u, v, w, x, z} (R := R) f m,
      ∀ q : PrimeSpectrum S, atPrimeOver.{u, v, w, x, z} (R := R) f q,
      ∀ m : MaximalSpectrum S, atMaximalOver.{u, v, w, x, z} (R := R) f m
    ] := sorry

end LinearMap.UniversallyInjective
