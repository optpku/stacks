module

public import ReasLib.RingTheory.Ideal.Regularity.Flat
import StacksCheckRecall

@[expose] public section

/- Lemma 23.7.6 (09PX): for a flat local map of Noetherian local rings with
regular closed fiber, finite Tor dimension of a regular-sequence quotient,
eventual residue-field Tor vanishing, and regularity of the source and relative
quotient ideals are equivalent. -/
universe u v

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable (f : R →+* S) [IsLocalHom f] (hflat : f.Flat)
variable (I : Ideal R) (J : Ideal S) (hIJ : I.map f ≤ J)
variable (hclosed : IsRegularLocalRing (f.Fiber (IsLocalRing.maximalIdeal R)))

@[stacks 09PX]
#check (RingHom.RegularSequenceQuotient.tfae_of_flat_of_regularClosedFiber
    f hflat I J hIJ hclosed :
  List.TFAE
    [ J.IsGeneratedByRegularSequence ∧
        (f.quotientByIdeals I J hIJ).HasFiniteTorDimension
    , J.IsGeneratedByRegularSequence ∧
        RingHom.RegularSequenceQuotient.ResidueTorEventuallyIsZero f I J hIJ
    , I.IsGeneratedByRegularSequence ∧
        (J.map (Ideal.Quotient.mk (I.map f))).IsGeneratedByRegularSequence
    ])

end

#check @RingHom.RegularSequenceQuotient.ResidueTorEventuallyIsZero
#check @RingHom.RegularSequenceQuotient.residueTorEventuallyIsZero_iff
#check @RingHom.RegularSequenceQuotient.finiteTor_iff_residueTor
#check @RingHom.RegularSequenceQuotient.finiteTor_iff_sourceRelative
#check @RingHom.RegularSequenceQuotient.residueTor_iff_sourceRelative
