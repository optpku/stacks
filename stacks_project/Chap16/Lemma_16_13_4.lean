/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
