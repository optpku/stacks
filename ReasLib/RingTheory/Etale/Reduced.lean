/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Etale
import ReasLib.RingTheory.Smooth.Reduced
import ReasLib.RingTheory.RingHom.FaithfullyFlat.Reduced

/-!
# Reducedness Along Étale Local Homomorphisms

Étale local homomorphisms between Noetherian local rings preserve and reflect reducedness.
-/

@[expose] public section

namespace RingHom.Etale

universe u v

/-- An étale local homomorphism between Noetherian local rings preserves and reflects reducedness. -/
theorem isReduced_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {f : A →+* B} [IsLocalHom f] (hf : f.Etale) :
    IsReduced A ↔ IsReduced B := sorry

end RingHom.Etale
