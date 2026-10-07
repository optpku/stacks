module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.FieldTheory.Separable.Generated
public import ReasLib.RingTheory.Smooth.Resolution.AtPrime
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.RingTheory.Ideal.MinimalPrime.Localization
import ReasLib.RingTheory.RegularLocalRing.Parameters.Lifting
import ReasLib.RingTheory.Smooth.Resolution.Localization
import ReasLib.RingTheory.Smooth.Resolution.Quotient

@[expose] public section

/-!
# Resolving maps over a field

This file packages the regular-local and separable-residue-field endpoint of
the primewise resolution argument.  No finite-type assumption is imposed on
the Noetherian target.
-/

universe u v w

namespace AlgHom.ResolvableAtPrime

variable {k : Type u} {A : Type v} {Λ : Type w}
variable [Field k] [CommRing A] [CommRing Λ]
variable [Algebra k A] [Algebra k Λ]

/-- Lemma 16.10.3 (Tag 07FE): over a field, a map from a finitely presented
algebra to a Noetherian algebra is resolvable at a minimal prime of its
transported singular ideal when the target local ring is regular and the
residue field is separable over the base. -/
@[stacks 07FE]
theorem of_regularLocal
    [Algebra.FinitePresentation k A] [IsNoetherianRing Λ]
    (φ : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hq : q.asIdeal ∈
      φ.singularIdealIn.minimalPrimes)
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)]
    [Algebra.IsSeparableOver k q.asIdeal.ResidueField] :
    φ.ResolvableAtPrime q := sorry

end AlgHom.ResolvableAtPrime
