module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.PuncturedSpectrum
import StacksCheckRecall

universe u v

/- Lemma 58.10.2 -/
@[stacks 0BLQ] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_fullyFaithful_of_connectedStrictHenselization :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] (Ash : Type v)
      [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
      [ConnectedSpace (AlgebraicGeometry.PuncturedSpectrum.scheme Ash)],
      Nonempty
        (AlgebraicGeometry.Scheme.finiteEtaleBaseChange
          (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A).ι).FullyFaithful)
