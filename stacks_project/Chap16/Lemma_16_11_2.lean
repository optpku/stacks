/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
