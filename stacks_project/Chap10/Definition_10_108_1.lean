/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Pure
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.108.1

@stack 04PR
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.108.1: an ideal `I ⊆ R` is pure when the quotient ring `R ⧸ I` is flat as an
`R`-module; this is the canonical owner predicate `Ideal.Pure I`, so no separate chapter-local
wrapper is needed here. -/
@[stacks 04PR]
#check @Ideal.Pure
