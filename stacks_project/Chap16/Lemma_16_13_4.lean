module

public import ReasLib.RingTheory.Approximation.Artin.Etale.AtPrime.Existence
import StacksCheckRecall

@[expose] public section

open PrimeSpectrum.ArtinApproximation

/- Lemma 16.13.4: primewise G-ring etale approximation is owned by
`AtPrime`. -/
@[stacks 0CAR]
#check @AtPrime.nonempty_of_isGRing

#check @MvPolynomial.IsSolution
#check @MvPolynomial.SolutionApproximation
#check @AtPrime
#check @AtPrime.spec
