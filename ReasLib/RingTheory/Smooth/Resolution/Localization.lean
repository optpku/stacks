module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.Map
public import ReasLib.RingTheory.Smooth.Factorization.SmoothAt
public import ReasLib.RingTheory.Smooth.Resolution.AtPrime

@[expose] public section

/-!
# Descending resolutions from a prime localization

The localized algebra homomorphism is the canonical
`AlgHom.localizeBaseAt`; no theorem-local algebra structures are needed.
-/

universe u v w

namespace AlgHom

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- The map `φ` is locally resolvable at `q` if its base-localized map to the
local ring at `q` is resolvable at the closed point.  The relative algebra
structure is confined here because Mathlib deliberately does not register it
globally. -/
@[stacks 07F9 "local resolvability at a target prime"]
def LocallyResolvableAt (φ : A →ₐ[R] Λ) (q : PrimeSpectrum Λ) : Prop :=
  -- Local instance justification (instance diamond): Mathlib intentionally keeps the
  -- canonical lies-over algebra structure out of global typeclass search.
  letI : Algebra (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  (φ.localizeBaseAt q).ResolvableAtPrime
    (IsLocalRing.closedPoint (Localization.AtPrime q.asIdeal))

namespace Factorisation.Finite.SmoothAt

/-- A resolution of the base-localized map descends to a finitely presented
factorisation whose transported singular ideal avoids the original prime. -/
@[stacks 07F9 "localized resolution descent"]
theorem nonempty_of_localization
    [IsNoetherianRing R] [Algebra.FinitePresentation R A]
    (φ : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hlocal : φ.LocallyResolvableAt q) :
    Nonempty (Factorisation.Finite.SmoothAt φ q) := sorry

end Factorisation.Finite.SmoothAt

namespace ResolvableAtPrime

namespace Localization

/-- Lemma 16.9.4 (Tag 07FA): a local resolution at a minimal prime descends
to a resolution of the original map when the target prime localization has
Krull dimension zero. -/
@[stacks 07FA]
theorem of_dimension_zero
    [IsNoetherianRing R] [Algebra.FinitePresentation R A]
    (φ : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hq : q.asIdeal ∈
      φ.singularIdealIn.minimalPrimes)
    (hlocal : φ.LocallyResolvableAt q)
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0) :
    φ.ResolvableAtPrime q := sorry

end Localization

end ResolvableAtPrime

end AlgHom
