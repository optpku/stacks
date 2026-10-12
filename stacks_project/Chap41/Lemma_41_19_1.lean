/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.Etale
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 41.19.1: an étale local homomorphism of Noetherian local rings preserves
Krull dimension. -/
@[stacks 039S]
#check
  (RingHom.Etale.ringKrullDim_eq :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      {f : A →+* B} [IsLocalHom f] (hf : f.Etale),
      ringKrullDim A = ringKrullDim B)
