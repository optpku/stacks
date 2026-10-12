/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.RegularLocal
import StacksCheckRecall

@[expose] public section

universe u v

/- Proposition 41.19.4: an étale local homomorphism between Noetherian local rings preserves
and reflects regular-locality. -/
@[stacks 025N] #check
  (RingHom.Etale.isRegularLocalRing_iff :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      {f : A →+* B} [IsLocalHom f], f.Etale →
        (IsRegularLocalRing A ↔ IsRegularLocalRing B))
