/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.CompleteIntersection.Local.GoodFactorization
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.RingTheory.RingHom.FiniteType.Noetherian

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
intersection if and only if all maps on completed local rings at target primes are complete
intersections in the good-factorization sense of 09QA. Target Noetherianity follows from finite
type; the completed maps need not themselves be of finite type. -/
@[stacks 09QE]
theorem isLocalCompleteIntersection_iff_completedLocalMap
    (f : A →+* B) (hfinite : f.FiniteType) :
    letI : IsNoetherianRing B := hfinite.isNoetherianRing
    f.IsLocalCompleteIntersection ↔
      ∀ q : PrimeSpectrum B, (f.completedLocalMap q).IsCompleteIntersection := sorry

/-- A local-complete-intersection map induces a complete-intersection homomorphism in the
good-factorization sense on completed local rings at every target prime. -/
theorem IsLocalCompleteIntersection.completedLocalMap
    {f : A →+* B} (hf : f.IsLocalCompleteIntersection) (q : PrimeSpectrum B) :
    letI : IsNoetherianRing B := hf.finiteType.isNoetherianRing
    (f.completedLocalMap q).IsCompleteIntersection :=
  (isLocalCompleteIntersection_iff_completedLocalMap f hf.finiteType).mp hf q

/-- A finite-type map is a local complete intersection when all of its completed local maps are
complete-intersection homomorphisms in the good-factorization sense. -/
theorem IsLocalCompleteIntersection.of_completedLocalMap
    {f : A →+* B} (hfinite : f.FiniteType)
    (hCompletion : letI : IsNoetherianRing B := hfinite.isNoetherianRing
      ∀ q : PrimeSpectrum B, (f.completedLocalMap q).IsCompleteIntersection) :
    f.IsLocalCompleteIntersection :=
  (isLocalCompleteIntersection_iff_completedLocalMap f hfinite).mpr hCompletion

end RingHom
