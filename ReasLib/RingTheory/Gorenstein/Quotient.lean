/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Gorenstein.Local
public import ReasLib.RingTheory.LocalRing.Quotient

@[expose] public section

universe u

namespace IsGorensteinLocalRing

/-- For a Noetherian commutative local ring, quotienting by a regular element
in the maximal ideal preserves and reflects Gorensteinness. -/
theorem iff_quotient_span_singleton
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : IsLocalRing.maximalIdeal A) (hf : IsRegular (f : A)) :
    IsGorensteinLocalRing A ↔
      IsGorensteinLocalRing (A ⧸ Ideal.span ({(f : A)} : Set A)) := sorry

end IsGorensteinLocalRing
