/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Reduced
import StacksCheckRecall

@[expose] public section

namespace RingHom.Etale

universe u v

/- Proposition 41.19.5: an étale local homomorphism of Noetherian local rings preserves
and reflects reducedness. -/
@[stacks 025O] #check
  (@RingHom.Etale.isReduced_iff :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      {f : A →+* B} [IsLocalHom f], f.Etale → (IsReduced A ↔ IsReduced B))

end RingHom.Etale
