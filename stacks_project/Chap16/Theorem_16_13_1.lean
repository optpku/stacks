/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
