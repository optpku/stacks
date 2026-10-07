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
