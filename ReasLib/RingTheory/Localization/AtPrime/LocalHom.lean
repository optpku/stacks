module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local maps into prime localizations

This leaf packages the standard maximal-ideal criterion for a map from a local
ring into a localization at a prime.  Mathlib supplies the two primitive facts:
`IsLocalRing.local_hom_TFAE` and `Localization.AtPrime.under_maximalIdeal`.
The criterion below is their map-level prime-localization specialization.
-/

@[expose] public section

universe u v

namespace Localization.AtPrime

variable {A : Type u} {S : Type v}
variable [CommRing A] [IsLocalRing A] [CommRing S]

/-- Tag `07BJ`: a map from a local ring to the localization of `S` at `q` is local exactly when
`q` contracts to the maximal ideal of the source. -/
@[stacks 07BJ "locality criterion for a map into a prime localization"]
theorem isLocalHom_iff_comap_maximalIdeal
    (f : A →+* S) (q : Ideal S) [q.IsPrime] :
    IsLocalHom ((algebraMap S (Localization.AtPrime q)).comp f) ↔
      Ideal.comap f q = IsLocalRing.maximalIdeal A := sorry

/-- Tag `07BJ`: a map into a prime localization is local when the selected prime contracts to
the maximal ideal of the local source. -/
@[stacks 07BJ "locality from contraction to the maximal ideal"]
theorem isLocalHom_of_comap_maximalIdeal
    (f : A →+* S) (q : Ideal S) [q.IsPrime]
    (hcomap : Ideal.comap f q = IsLocalRing.maximalIdeal A) :
    IsLocalHom ((algebraMap S (Localization.AtPrime q)).comp f) := sorry

/-- Tag `07BJ`: the canonical algebra map into a prime localization is local when the selected
prime contracts to the maximal ideal of the local base. -/
@[stacks 07BJ "local algebra map into a prime localization"]
theorem algebraMap_isLocalHom_of_comap_maximalIdeal
    [Algebra A S] (q : Ideal S) [q.IsPrime]
    (hcomap : Ideal.comap (algebraMap A S) q = IsLocalRing.maximalIdeal A) :
    IsLocalHom (algebraMap A (Localization.AtPrime q)) := sorry

end Localization.AtPrime
