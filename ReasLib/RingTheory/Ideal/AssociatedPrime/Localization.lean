/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open IsLocalRing

/-!
# Exact associated primes over localizations
-/

universe u v w

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module A M] [Module R M]
variable [IsScalarTower R A M]

/-- Exact associated primes of a module over a localization, contracted to the
base ring, are exactly the exact associated primes after restriction of scalars. -/
@[stacks 05BZ]
theorem associatedPrimesOfModule_image_comap_eq_of_isLocalization (T : Submonoid R)
    [IsLocalization T A] :
    Ideal.comap (algebraMap R A) '' associatedPrimesOfModule A M =
      associatedPrimesOfModule R M := sorry

end

section

variable {R : Type u} [CommRing R]
variable (T : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The exact associated primes of a localized module agree with the contractions of its exact
associated primes over the localization. -/
@[stacks 05BZ]
theorem associatedPrimesOfModule_localizedModule_eq_image_comap :
    Ideal.comap (algebraMap R (Localization T)) ''
        associatedPrimesOfModule (Localization T) (LocalizedModule T M) =
      associatedPrimesOfModule R (LocalizedModule T M) := sorry

end

namespace Ideal.IsAssociatedToModule.Localization

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Exact association at a prime ascends to exact association of the maximal ideal after
localization at that prime. -/
@[stacks 0310 "exact associated prime ascends to the local maximal ideal"]
theorem maximalIdeal_atPrime {p : Ideal R} [p.IsPrime]
    (hp : Ideal.IsAssociatedToModule R M p) :
    Ideal.IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
      (maximalIdeal (Localization.AtPrime p)) := sorry

/-- Exact association of the local maximal ideal descends along localization when the original
prime is finitely generated. -/
@[stacks 0310 "finitely generated local maximal ideal descends"]
theorem of_maximalIdeal_atPrime {p : Ideal R} [p.IsPrime]
    (hp :
      Ideal.IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
        (maximalIdeal (Localization.AtPrime p)))
    (hfg : p.FG) :
    Ideal.IsAssociatedToModule R M p := sorry

/-- For a finitely generated prime, exact association is equivalent to exact association of the
maximal ideal after localization at that prime. -/
@[stacks 0310 "localization criterion for finitely generated exact associated primes"]
theorem iff_maximalIdeal_atPrime {p : Ideal R} [p.IsPrime] (hfg : p.FG) :
    Ideal.IsAssociatedToModule R M p ↔
      Ideal.IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
        (maximalIdeal (Localization.AtPrime p)) := sorry

variable (T : Submonoid R)

/-- If every denominator acts regularly, exact association of a fixed prime is unchanged when the
module is localized and then viewed over the base ring. -/
@[stacks 05C0 "pointwise exact association under localization by regular elements"]
theorem iff_of_isSMulRegular {p : Ideal R}
    (hT : ∀ t : T, IsSMulRegular M t) :
    Ideal.IsAssociatedToModule R M p ↔
      Ideal.IsAssociatedToModule R (LocalizedModule T M) p := sorry

end Ideal.IsAssociatedToModule.Localization

namespace associatedPrimesOfModule.Localization

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Membership in the exact associated-prime set ascends to membership of the local maximal ideal
after localization at that prime. -/
@[stacks 0310 "exact associated-prime membership ascends to the local maximal ideal"]
theorem maximalIdeal_mem_atPrime {p : Ideal R} [p.IsPrime]
    (hp : p ∈ associatedPrimesOfModule R M) :
    maximalIdeal (Localization.AtPrime p) ∈
      associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := sorry

/-- Membership of the local maximal ideal descends to a finitely generated exact associated
prime. -/
@[stacks 0310 "local maximal-ideal membership descends to a finitely generated prime"]
theorem mem_of_maximalIdeal_mem_atPrime {p : Ideal R} [p.IsPrime]
    (hp :
      maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M))
    (hfg : p.FG) :
    p ∈ associatedPrimesOfModule R M := sorry

/-- For a finitely generated prime, membership in the exact associated-prime set is detected by
the maximal ideal after localization at that prime. -/
@[stacks 0310 "set-level localization criterion for finitely generated exact associated primes"]
theorem mem_iff_maximalIdeal_mem_atPrime {p : Ideal R} [p.IsPrime] (hfg : p.FG) :
    p ∈ associatedPrimesOfModule R M ↔
      maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := sorry

variable (T : Submonoid R)

/-- An exact associated prime disjoint from the denominator submonoid remains exact associated
after localization, with the localized module viewed over the base ring. -/
@[stacks 05BZ "pointwise persistence of a disjoint exact associated prime"]
theorem mem_localizedModule {p : Ideal R}
    (hp : p ∈ associatedPrimesOfModule R M)
    (hT : Disjoint (T : Set R) (p : Set R)) :
    p ∈ associatedPrimesOfModule R (LocalizedModule T M) := sorry

/-- Exact associated primes disjoint from a submonoid remain exact associated primes after
localization, with the localized module viewed over the base ring. -/
@[stacks 05BZ "disjoint exact associated primes persist under localization"]
theorem inter_disjoint_subset :
    associatedPrimesOfModule R M ∩
        { p : Ideal R | Disjoint (T : Set R) (p : Set R) } ⊆
      associatedPrimesOfModule R (LocalizedModule T M) := sorry

/-- Range formulation of persistence of exact associated primes under localization. -/
@[stacks 05BZ "range form of exact associated-prime persistence"]
theorem inter_range_subset :
    associatedPrimesOfModule R M ∩
        Set.range (Ideal.comap (algebraMap R (Localization T))) ⊆
      associatedPrimesOfModule R (LocalizedModule T M) := sorry

/-- Over a Noetherian ring, exact associated primes of a localized module are exactly the exact
associated primes of the original module disjoint from the localization submonoid. -/
@[stacks 05BZ "Noetherian exact associated primes under localization"]
theorem inter_disjoint_eq [IsNoetherianRing R] :
    associatedPrimesOfModule R M ∩
        { p : Ideal R | Disjoint (T : Set R) (p : Set R) } =
      associatedPrimesOfModule R (LocalizedModule T M) := sorry

/-- Range formulation of the Noetherian exact associated-prime localization equality. -/
@[stacks 05BZ "range form of Noetherian exact associated-prime localization"]
theorem inter_range_eq [IsNoetherianRing R] :
    associatedPrimesOfModule R M ∩
        Set.range (Ideal.comap (algebraMap R (Localization T))) =
      associatedPrimesOfModule R (LocalizedModule T M) := sorry

/-- Over a Noetherian ring, a prime is exact associated to the localized module exactly when it
was exact associated before localization and is disjoint from the denominator submonoid. -/
@[stacks 05BZ "pointwise Noetherian exact associated-prime localization criterion"]
theorem mem_localizedModule_iff [IsNoetherianRing R] {p : Ideal R} :
    p ∈ associatedPrimesOfModule R (LocalizedModule T M) ↔
      p ∈ associatedPrimesOfModule R M ∧
        Disjoint (T : Set R) (p : Set R) := sorry

/-- If every denominator acts regularly, exact association is unchanged when the module is
localized and then viewed over the base ring. -/
@[stacks 05C0 "pointwise exact association under localization by regular elements"]
theorem mem_iff_of_isSMulRegular {p : Ideal R}
    (hT : ∀ t : T, IsSMulRegular M t) :
    p ∈ associatedPrimesOfModule R M ↔
      p ∈ associatedPrimesOfModule R (LocalizedModule T M) := sorry

/-- If every denominator acts regularly, localization does not change the exact associated-prime
set when the localized module is viewed over the base ring. -/
@[stacks 05C0 "exact associated primes under localization by regular elements"]
theorem eq_of_isSMulRegular (hT : ∀ t : T, IsSMulRegular M t) :
    associatedPrimesOfModule R M =
      associatedPrimesOfModule R (LocalizedModule T M) := sorry

end associatedPrimesOfModule.Localization

namespace associatedPrimes.Localization

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (T : Submonoid R)

/-- Over a Noetherian ring, associated primes of a localized module are exactly the associated
primes of the original module disjoint from the localization submonoid. -/
@[stacks 05BZ "Noetherian associated primes under localization"]
theorem inter_disjoint_eq [IsNoetherianRing R] :
    associatedPrimes R M ∩
        { p : Ideal R | Disjoint (T : Set R) (p : Set R) } =
      associatedPrimes R (LocalizedModule T M) := sorry

/-- Range formulation of the Noetherian associated-prime localization equality. -/
@[stacks 05BZ "range form of Noetherian associated-prime localization"]
theorem inter_range_eq [IsNoetherianRing R] :
    associatedPrimes R M ∩
        Set.range (Ideal.comap (algebraMap R (Localization T))) =
      associatedPrimes R (LocalizedModule T M) := sorry

/-- Over a Noetherian ring, membership in the associated-prime set after localization is
equivalent to original membership together with disjointness from the denominators. -/
@[stacks 05BZ "pointwise Noetherian associated-prime localization criterion"]
theorem mem_localizedModule_iff [IsNoetherianRing R] {p : Ideal R} :
    p ∈ associatedPrimes R (LocalizedModule T M) ↔
      p ∈ associatedPrimes R M ∧ Disjoint (T : Set R) (p : Set R) := sorry

/-- If every denominator acts regularly, localization does not change the associated-prime set
when the localized module is viewed over a Noetherian base ring. -/
@[stacks 05C0 "associated primes under localization by regular elements"]
theorem eq_of_isSMulRegular [IsNoetherianRing R]
    (hT : ∀ t : T, IsSMulRegular M t) :
    associatedPrimes R M =
      associatedPrimes R (LocalizedModule T M) := sorry

end associatedPrimes.Localization

namespace Ideal

/-- Deprecated compatibility spelling for
`Ideal.IsAssociatedToModule.Localization.of_maximalIdeal_atPrime`. -/
@[deprecated Ideal.IsAssociatedToModule.Localization.of_maximalIdeal_atPrime
    (since := "2026-08-07"), stacks 0310 "deprecated exact-association descent spelling"]
theorem isAssociatedToModule_of_isAssociatedToModule_maximalIdeal_atPrime_of_fg
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {p : Ideal R} [p.IsPrime]
    (hp :
      IsAssociatedToModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)
        (maximalIdeal (Localization.AtPrime p)))
    (hfg : p.FG) :
    IsAssociatedToModule R M p := sorry

end Ideal

/-- Deprecated compatibility spelling for
`associatedPrimesOfModule.Localization.maximalIdeal_mem_atPrime`. -/
@[deprecated associatedPrimesOfModule.Localization.maximalIdeal_mem_atPrime
    (since := "2026-08-07"), stacks 0310 "deprecated exact associated-prime ascent spelling"]
theorem mem_associatedPrimesOfModule_atPrime_of_mem_associatedPrimesOfModule
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {p : Ideal R} [p.IsPrime] (hp : p ∈ associatedPrimesOfModule R M) :
    maximalIdeal (Localization.AtPrime p) ∈
      associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := sorry

/-- Deprecated compatibility spelling for
`associatedPrimesOfModule.Localization.inter_range_subset`. -/
@[deprecated associatedPrimesOfModule.Localization.inter_range_subset
    (since := "2026-08-07"), stacks 05BZ "deprecated localization-range inclusion spelling"]
theorem associatedPrimesOfModule_inter_localization_range_subset
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (S : Submonoid R) :
    associatedPrimesOfModule R M ∩
        Set.range (Ideal.comap (algebraMap R (Localization S))) ⊆
      associatedPrimesOfModule R (LocalizedModule S M) := sorry

/-- Deprecated compatibility spelling for
`associatedPrimesOfModule.Localization.inter_range_eq`. -/
@[deprecated associatedPrimesOfModule.Localization.inter_range_eq
    (since := "2026-08-07"), stacks 05BZ "deprecated Noetherian localization-range equality spelling"]
theorem associatedPrimesOfModule_inter_localization_range_eq
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (S : Submonoid R) :
    associatedPrimesOfModule R M ∩
        Set.range (Ideal.comap (algebraMap R (Localization S))) =
      associatedPrimesOfModule R (LocalizedModule S M) := sorry

/-- Deprecated compatibility spelling for
`associatedPrimesOfModule.Localization.inter_disjoint_eq`. -/
@[deprecated associatedPrimesOfModule.Localization.inter_disjoint_eq
    (since := "2026-08-07"), stacks 05BZ "deprecated Noetherian localization-disjointness equality spelling"]
theorem associatedPrimesOfModule_inter_disjoint_eq_localizedModule
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (S : Submonoid R) :
    associatedPrimesOfModule R M ∩
        { p : Ideal R | Disjoint (S : Set R) (p : Set R) } =
      associatedPrimesOfModule R (LocalizedModule S M) := sorry

/-- Deprecated compatibility spelling for
`associatedPrimesOfModule.Localization.eq_of_isSMulRegular`. -/
@[deprecated associatedPrimesOfModule.Localization.eq_of_isSMulRegular
    (since := "2026-08-07"), stacks 05C0 "deprecated regular-denominator localization spelling"]
theorem associatedPrimesOfModule_eq_associatedPrimesOfModule_localizedModule
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (S : Submonoid R) (hS : ∀ s : S, IsSMulRegular M s) :
    associatedPrimesOfModule R M =
      associatedPrimesOfModule R (LocalizedModule S M) := sorry
