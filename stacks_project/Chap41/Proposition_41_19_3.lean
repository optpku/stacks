module

public import ReasLib.RingTheory.CohenMacaulay.Etale
import StacksCheckRecall

@[expose] public section

universe u v

/- Proposition 41.19.3: an étale local homomorphism of Noetherian local rings preserves and
reflects the Cohen–Macaulay property. -/
@[stacks 025Q] #check
  (RingHom.Etale.cohenMacaulay_iff :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      {f : A →+* B} [IsLocalHom f], f.Etale →
        (Module.CohenMacaulay A A ↔ Module.CohenMacaulay B B))
