module

public import ReasLib.RingTheory.Approximation.Artin.Local
import StacksCheckRecall

@[expose] public section

/- Theorem 16.13.1: the source-facing G-ring branch is owned by the reusable
`HenselianLocalRing.ArtinApproximation` API. -/
@[stacks 07QY]
#check @HenselianLocalRing.ArtinApproximation.nonempty_of_isGRing

#check @MvPolynomial.IsSolution
#check @MvPolynomial.SolutionApproximation
