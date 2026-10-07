module

public import ReasLib.RingTheory.Etale.Depth
import StacksCheckRecall

@[expose] public section

universe u v

/- Proposition 41.19.2: an étale local homomorphism of Noetherian local rings preserves
ring depth. -/
@[stacks 039T] #check
  (RingHom.Etale.moduleDepth_eq :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      {f : A →+* B} [IsLocalHom f], f.Etale → moduleDepth A A = moduleDepth B B)
