/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.Regular.RingMap

@[expose] public section

/-!
# G-rings

@stack 07GH
@stack 0AH2

This module owns the primewise completion formulation of G-rings.  The completed
local ring and its functorial map remain in the shorter `PrimeSpectrum` API.
-/

open IsLocalRing

universe u

/-- A commutative ring is a G-ring when it is Noetherian
and every prime-local completion map is regular. -/
@[stacks 07GH]
class IsGRing (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  /-- The completion map at every prime localization is regular. -/
  regular_localization_completion (p : PrimeSpectrum R) :
    (algebraMap (Localization.AtPrime p.asIdeal) (R̂[p])).Regular

/-- A Noetherian ring is a G-ring exactly when every prime-local completion
map is regular. -/
@[stacks 07GH "G-ring primewise completion criterion"]
theorem isGRing_iff_forall_regular_localization_completion
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔ ∀ p : PrimeSpectrum R,
      (algebraMap (Localization.AtPrime p.asIdeal) (R̂[p])).Regular := sorry

namespace IsGRing

namespace AdicCompletion

/-- Every adic completion map of a G-ring is regular. -/
@[stacks 0AH2]
instance regularMap
    {A : Type u} [CommRing A] [IsGRing A] (I : Ideal A) :
    (algebraMap A (AdicCompletion I A)).Regular := sorry

end AdicCompletion

end IsGRing
