/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Approximation.LocalArtinian
import StacksCheckRecall

@[expose] public section

open Algebra.LocalArtinianApproximation

/- Lemma 16.11.2: polynomial factorization through a local Artinian quotient
is owned by `PolynomialFactorisation.Capture`. -/
@[stacks 07FH]
#check @PolynomialFactorisation.Capture.nonempty

#check @PolynomialFactorisation
#check @PolynomialFactorisation.Capture
