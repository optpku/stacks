/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Essential
public import ReasLib.RingTheory.Unramified.LocalRing

@[expose] public section

universe u v

namespace RingHom.EssEtale

/-- A local homomorphism between commutative Noetherian local rings is essentially
étale exactly when it is flat, formally unramified, and essentially of finite type. -/
theorem iff_localRing
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {f : A →+* B} [IsLocalHom f] :
    f.EssEtale ↔ f.Flat ∧ (f.FormallyUnramified ∧ f.EssFiniteType) := sorry

end RingHom.EssEtale

end
