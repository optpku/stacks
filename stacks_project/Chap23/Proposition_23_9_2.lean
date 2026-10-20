module

public import ReasLib.RingTheory.CompleteIntersection.Local.CompletionTor
import StacksCheckRecall

@[expose] public section

/- Proposition 23.9.2 (09QB): for a local homomorphism of Noetherian local
rings, the target is a complete intersection with eventually vanishing Tor
against the source residue field if and only if the source is a complete
intersection and the induced map on completions is a local complete
intersection. -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable (f : A →+* B) [IsLocalHom f]

@[stacks 09QB]
#check (RingHom.CompleteIntersection.target_and_tor_iff_source_and_completion f :
  (IsCompleteIntersectionLocalRing B ∧ f.torEventuallyIsZeroAtResidueField) ↔
    (IsCompleteIntersectionLocalRing A ∧
      (AdicCompletion.mapLocal f).IsLocalCompleteIntersection))

end

#check @RingHom.torEventuallyIsZeroAtResidueField
#check @RingHom.CompleteIntersection.source_of_target_of_tor
#check @RingHom.CompleteIntersection.completion_of_target_of_tor
#check @RingHom.CompleteIntersection.target_of_source_of_completion
#check @RingHom.CompleteIntersection.tor_of_source_of_completion
