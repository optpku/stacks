module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.RingTheory.AdicCompletion.LocalMap

/-!
# Local homomorphisms on maximal-ideal completions

The map on maximal-ideal completions induced by a local homomorphism of
Noetherian local rings is again a local homomorphism.
-/

@[expose] public section

universe u v

namespace AdicCompletion.mapLocal

/-- The map on maximal-ideal completions induced by a local homomorphism of
Noetherian local rings is itself local. -/
instance isLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] :
    IsLocalHom (AdicCompletion.mapLocal f) := sorry

end AdicCompletion.mapLocal
