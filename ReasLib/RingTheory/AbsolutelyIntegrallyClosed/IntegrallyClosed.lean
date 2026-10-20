/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed.Localization

@[expose] public section

/-!
# Descent of absolute integral closedness

The primary theorem is stated for an arbitrary integrally closed embedding. The
fraction-ring criteria are consequences at the natural `IsFractionRing` layer and
for Mathlib's canonical `FractionRing` model.

@stack 0DCP
@stack 0DCQ
-/

universe u v

namespace IsIntegrallyClosedIn

/-- An integrally closed subring of an absolutely integrally closed algebra is
absolutely integrally closed. -/
@[stacks 0DCP "descent of absolute integral closedness"]
theorem isAbsolutelyIntegrallyClosed {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] [IsIntegrallyClosedIn A B]
    [IsAbsolutelyIntegrallyClosed B] : IsAbsolutelyIntegrallyClosed A := sorry
-- Proof strategy: take a root in `B` using `IsAbsolutelyIntegrallyClosed.exists_root`, descend
-- its integral value via `IsIntegrallyClosedIn.algebraMap_eq_of_integral`, transport the root
-- equation by injectivity, and apply `IsAbsolutelyIntegrallyClosed.of_exists_root`.

end IsIntegrallyClosedIn

namespace IsAbsolutelyIntegrallyClosed

/-- An integrally closed ring inside an arbitrary fraction-field model is
absolutely integrally closed exactly when that field is algebraically closed. -/
@[stacks 0DCQ "absolute integral closedness in an arbitrary fraction ring"]
theorem iff_isAlgClosed_of_isFractionRing {A : Type u} {K : Type v} [CommRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosedIn A K] :
    IsAbsolutelyIntegrallyClosed A ↔ IsAlgClosed K := sorry
-- Proof strategy: prove both directions with
-- `IsIntegrallyClosedIn.isAbsolutelyIntegrallyClosed` and the fraction-field root criterion,
-- transporting polynomials along `IsFractionRing`.

/-- A normal domain is absolutely integrally closed exactly when its canonical
fraction field is algebraically closed. -/
@[stacks 0DCQ "absolute integral closedness and the canonical fraction ring"]
theorem iff_isAlgClosed_fractionRing (A : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] :
    IsAbsolutelyIntegrallyClosed A ↔ IsAlgClosed (FractionRing A) := sorry
-- Proof strategy: specialize `iff_isAlgClosed_of_isFractionRing` to the canonical
-- `FractionRing` algebra and its `IsIntegrallyClosedIn` instance.

end IsAbsolutelyIntegrallyClosed
