/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Etale.Depth
public import ReasLib.RingTheory.KrullDimension.Etale

@[expose] public section

namespace RingHom.Etale

universe u v

/-- An étale local homomorphism of Noetherian local rings preserves and reflects the
Cohen–Macaulay property. -/
@[stacks 025Q]
theorem cohenMacaulay_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {f : A →+* B} [IsLocalHom f] (hf : f.Etale) :
    Module.CohenMacaulay A A ↔ Module.CohenMacaulay B B := sorry

end RingHom.Etale
