module

public import ReasLib.RingTheory.Normal.Etale
import StacksCheckRecall

@[expose] public section

universe u v

/- Proposition 41.19.7: an étale local homomorphism between Noetherian local rings preserves
and reflects the normal-domain property. -/
@[stacks 025P] #check (RingHom.Etale.isNormalRing_iff :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {f : A →+* B} [IsLocalHom f], f.Etale → (IsNormalRing A ↔ IsNormalRing B))
