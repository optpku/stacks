/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.LinearProjection
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Complex.Basic
import StacksCheckRecall

/- Exercise 111.55.7. A nonconstant complex polynomial in two variables admits a finite
projection defined by a linear form. -/
@[stacks 07DL] #check (MvPolynomial.exists_linearFormAeval_finite :
  ∀ (f : MvPolynomial (Fin 2) ℂ), 0 < f.totalDegree →
    ∃ α β : ℂ, (MvPolynomial.linearFormAeval f α β).Finite)
