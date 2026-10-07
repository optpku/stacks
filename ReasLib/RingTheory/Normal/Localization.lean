module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Ring

/-!
# Normality under localization

This leaf records that normality is stable under arbitrary models of a ring
localization, together with the canonical instance for `Localization M`.
-/

@[expose] public section

universe u v

namespace IsNormalRing

/-- An arbitrary localization of a normal commutative ring is normal. -/
@[stacks 037C]
theorem of_isLocalization
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [IsNormalRing R] :
    IsNormalRing S := sorry

end IsNormalRing

namespace Localization

/-- The canonical localization of a normal ring is normal. -/
@[stacks 037C "normal localization instance"]
instance instIsNormalRing
    {R : Type u} [CommRing R] (M : Submonoid R) [IsNormalRing R] :
    IsNormalRing (Localization M) := sorry

end Localization
