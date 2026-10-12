/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.LocalRing
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 41.11.1: a local homomorphism of Noetherian local rings is essentially
étale exactly when it is flat, formally unramified, and essentially of finite type. -/
@[stacks 0258] #check (RingHom.EssEtale.iff_localRing :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {f : A →+* B} [IsLocalHom f],
    f.EssEtale ↔ f.Flat ∧ (f.FormallyUnramified ∧ f.EssFiniteType))

end
