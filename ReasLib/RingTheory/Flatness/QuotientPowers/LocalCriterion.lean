module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Flat.Localization
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.LocalCriterion
public import ReasLib.RingTheory.Flatness.QuotientPowers
public import ReasLib.RingTheory.Flatness.QuotientPowers.ClosedFiber
public import ReasLib.RingTheory.Flatness.QuotientPowers.Kernel
public import ReasLib.RingTheory.Ideal.Localization

/-!
# Local criteria from ideal-power quotients

This leaf owns the local and prime-local conclusions attached to the `Module.Flat.QuotientPowers`
predicate.  The quotient-power hypothesis remains explicit; no global flatness or localization
instance is manufactured by the API.

@stack 0523
-/

@[expose] public section

universe u v w

namespace Module.Flat.QuotientPowers

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/-- If all positive ideal-power quotients are flat, the localization at a prime containing the
extended ideal is flat over the original base ring. -/
@[stacks 0523 "local quotient-power criterion at a prime"]
theorem atPrime
    (I : Ideal R) (q : PrimeSpectrum S)
    (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : Module.Flat.QuotientPowers (M := M) I) :
    Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := sorry

/-- Over a local target ring, ideal-power quotient flatness implies flatness of the whole module. -/
@[stacks 0523 "local quotient-power criterion"]
theorem of_isLocalRing
    [IsLocalRing S] (I : Ideal R)
    (hI : I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S)
    (hflat : Module.Flat.QuotientPowers (M := M) I) :
    Module.Flat R M := sorry

end Module.Flat.QuotientPowers
