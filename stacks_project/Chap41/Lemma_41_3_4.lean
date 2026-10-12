/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.LocalMap.Unramified
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 41.3.4: For an essentially finite type local homomorphism of Noetherian local rings,
unramifiedness as a local homomorphism is equivalent to unramifiedness of the induced map on
maximal-ideal completions, both as a local homomorphism and in the ordinary finite-type sense. -/
@[stacks 039I]
#check
  (AdicCompletion.LocalMap.unramified_tfae :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      (f : A →+* B) [IsLocalHom f] (h_essentiallyFiniteType : f.EssFiniteType),
      List.TFAE [
        f.FormallyUnramified,
        (AdicCompletion.mapLocal f).FormallyUnramified ∧
          (AdicCompletion.mapLocal f).EssFiniteType,
        (AdicCompletion.mapLocal f).Unramified])
