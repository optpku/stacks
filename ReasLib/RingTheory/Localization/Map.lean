/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Algebra structures on maps of localizations

This file provides the canonical algebra structure induced by a ring map that carries one
denominator submonoid into another. It is a named construction rather than a global instance, so
that users can select it without introducing localization diamonds.

@stack 07F9
-/

@[expose] public section

universe u v

namespace Localization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {S : Submonoid A} {S' : Submonoid B}

/-- The algebra structure on `Localization S → Localization S'` induced by `A → B` when the
image of `S` lies in `S'`. -/
@[stacks 07F9 "localization map algebra structure", implicit_reducible]
noncomputable def mapAlgebra (h : S ≤ S'.comap (algebraMap A B)) :
    Algebra (Localization S) (Localization S') :=
  RingHom.toAlgebra (IsLocalization.map (Localization S') (algebraMap A B) h)

/-- Under `mapAlgebra`, a localized base-ring element is sent by first applying
`A → B` and then the canonical map into the target localization.  The local
algebra structure is the named, non-global action selected by `h`. -/
@[simp, stacks 07F9 "localization map algebra computation"]
theorem mapAlgebra_algebraMap (h : S ≤ S'.comap (algebraMap A B)) (x : A) :
    letI : Algebra (Localization S) (Localization S') := mapAlgebra h
    algebraMap (Localization S) (Localization S')
        (algebraMap A (Localization S) x) =
      algebraMap B (Localization S') (algebraMap A B x) := sorry

end Localization

namespace AlgHom

universe w

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- For a target prime `q`, the image in `A` of the complement of its
contraction to `R` maps into the complement of `q`. -/
theorem baseLocalizationSubmonoid_le (f : A →ₐ[R] Λ)
    (q : PrimeSpectrum Λ) :
    Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.asIdeal.under R)) ≤
      Submonoid.comap f.toRingHom q.asIdeal.primeCompl := sorry

/-- The underlying ring homomorphism from the base localization of `A` at the
contraction of `q` to the local ring `Λ_q`. -/
noncomputable def localizeBaseAtRingHom (f : A →ₐ[R] Λ)
    (q : PrimeSpectrum Λ) :
    Localization
        (Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.asIdeal.under R))) →+*
      Localization.AtPrime q.asIdeal :=
  IsLocalization.map (Localization.AtPrime q.asIdeal) f.toRingHom
    (baseLocalizationSubmonoid_le f q)

/-- The localized ring homomorphism commutes with the maps from the local ring
of the base at the contracted prime. -/
theorem localizeBaseAtRingHom_commutes (f : A →ₐ[R] Λ)
    (q : PrimeSpectrum Λ) (x : Localization.AtPrime (q.asIdeal.under R)) :
    -- Local instance justification (instance diamond): Mathlib deliberately leaves this
    -- canonical lies-over algebra structure out of global typeclass search.
    letI : Algebra (Localization.AtPrime (q.asIdeal.under R))
        (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    localizeBaseAtRingHom f q
        (algebraMap
          (Localization.AtPrime (q.asIdeal.under R))
          (Localization
            (Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.asIdeal.under R)))) x) =
      algebraMap
        (Localization.AtPrime (q.asIdeal.under R))
        (Localization.AtPrime q.asIdeal) x := sorry

/-- An `R`-algebra homomorphism `A → Λ` induces an algebra homomorphism
from the base localization of `A` at `q ∩ R` to `Λ_q`, over `R_{q ∩ R}`. -/
@[stacks 07F9 "base localization at a target prime"]
noncomputable def localizeBaseAt (f : A →ₐ[R] Λ) (q : PrimeSpectrum Λ) :
    -- Local instance justification (instance diamond): the codomain algebra is canonical,
    -- but registering it globally would create the localization diamonds documented by Mathlib.
    letI : Algebra (Localization.AtPrime (q.asIdeal.under R))
        (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    Localization
        (Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.asIdeal.under R))) →ₐ[
          Localization.AtPrime (q.asIdeal.under R)]
      Localization.AtPrime q.asIdeal :=
  -- Local instance justification (instance diamond): construct the `AlgHom` using exactly the
  -- lies-over algebra structure fixed in its public result type.
  letI : Algebra (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  { __ := localizeBaseAtRingHom f q
    commutes' := localizeBaseAtRingHom_commutes f q }

/-- On elements of `A`, `localizeBaseAt` is the original map followed by the
canonical map to `Λ_q`. -/
@[simp]
theorem localizeBaseAt_algebraMap (f : A →ₐ[R] Λ)
    (q : PrimeSpectrum Λ) (x : A) :
    -- Local instance justification (instance diamond): state the computation using the same
    -- non-global lies-over algebra structure as `localizeBaseAt`.
    letI : Algebra (Localization.AtPrime (q.asIdeal.under R))
        (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    localizeBaseAt f q
        (algebraMap A
          (Localization
            (Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.asIdeal.under R)))) x) =
      algebraMap Λ (Localization.AtPrime q.asIdeal) (f x) := sorry

end AlgHom
