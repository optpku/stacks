/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom

@[expose] public section

/-!
# Local Complete Intersection Maps at Completed Local Rings

This leaf gives the primewise completed-local criterion for a finite-type ring homomorphism over
a Noetherian source. The completed-local map is exposed through the map-first `RingHom` API.
-/

universe u v

namespace RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsNoetherianRing A]

/-- Lemma 23.9.5 (Tag 09QE): a finite-type map from a Noetherian ring is a local complete
intersection if and only if all maps on completed local rings at target primes are local complete
intersections. -/
@[stacks 09QE]
theorem isLocalCompleteIntersection_iff_completedLocalMap
    (f : A →+* B) (hfinite : f.FiniteType) :
    f.IsLocalCompleteIntersection ↔
      ∀ q : PrimeSpectrum B, (f.completedLocalMap q).IsLocalCompleteIntersection := sorry

/-- A finite-type local-complete-intersection map induces a local complete intersection on every
completed local ring at a target prime. -/
theorem IsLocalCompleteIntersection.completedLocalMap
    {f : A →+* B} (hf : f.IsLocalCompleteIntersection) (q : PrimeSpectrum B) :
    (f.completedLocalMap q).IsLocalCompleteIntersection := sorry

/-- A finite-type map is a local complete intersection when all of its completed local maps are
local complete intersections. -/
theorem IsLocalCompleteIntersection.of_completedLocalMap
    {f : A →+* B} (hfinite : f.FiniteType)
    (hCompletion : ∀ q : PrimeSpectrum B,
      (f.completedLocalMap q).IsLocalCompleteIntersection) :
    f.IsLocalCompleteIntersection := sorry

end RingHom
