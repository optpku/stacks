/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.LaurentPolynomial
import StacksCheckRecall

@[expose] public section

/-!
# Laurent Polynomial N-1 Descent

@stack 032J

The reusable Laurent-polynomial descent theorem is owned by ReasLib; this
chapter file retains the textbook entry point.
-/

-- Lemma 10.161.6, tag `032J`: if `R[T;T⁻¹]` is `N-1` for a Noetherian
-- domain `R`, then `R` is `N-1`.
@[stacks 032J]
#check @IsN1Ring.of_laurentPolynomial
