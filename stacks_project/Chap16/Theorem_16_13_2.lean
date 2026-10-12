/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Approximation.Artin.Etale.AtClosedPoint.Existence
import StacksCheckRecall

@[expose] public section

open PrimeSpectrum.ArtinApproximation

/- Theorem 16.13.2: the source-facing local G-ring branch is owned by
`AtClosedPoint`. -/
@[stacks 07QZ]
#check @AtClosedPoint.nonempty_of_isGRing

#check @MvPolynomial.IsSolution
#check @MvPolynomial.SolutionApproximation
#check @AtClosedPoint
#check @AtClosedPoint.spec
