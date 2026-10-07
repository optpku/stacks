module

public import Mathlib.RingTheory.RingHom.Etale
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Normal
public import ReasLib.RingTheory.Smooth.Normal

/-!
# Normality Under Étale Local Homomorphisms

Normality is preserved and reflected by étale local homomorphisms between
Noetherian local rings.
-/

@[expose] public section

namespace RingHom.Etale

universe u v

/-- An étale local homomorphism between Noetherian local rings preserves and reflects normality. -/
@[stacks 025P]
theorem isNormalRing_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {f : A →+* B} [IsLocalHom f] (hf : f.Etale) :
    IsNormalRing A ↔ IsNormalRing B := sorry

end RingHom.Etale
