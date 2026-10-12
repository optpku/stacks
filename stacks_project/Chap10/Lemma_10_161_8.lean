/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.161.8

@stack 032L
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.161.8: if `R` is a Noetherian normal domain with fraction field `K` and `L / K` is a
finite separable field extension, then the integral closure of `R` in `L` is finite over `R`.
This is the canonical theorem `IsIntegralClosure.finite`. -/
@[stacks 032L]
#check @IsIntegralClosure.finite
