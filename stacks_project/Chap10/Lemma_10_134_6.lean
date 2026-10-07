module

public import ReasLib.RingTheory.Extension.Cotangent.Surjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.134.6

@stack 07BP
-/

/- Lemma 10.134.6 [stacks 07BP]: canonical recall.  The source writes the
same-universe conormal module directly.  `Lift` is the universe-polymorphic
formalization of that degree-one term, so the ReasLib statement is strictly
more reusable while expressing the same concentration phenomenon. -/

@[stacks 07BP "(1), surjective naive cotangent complex"]
#check @Algebra.NaiveCotangent.Surjective.homotopyEquivSingleOne
#check @Algebra.Extension.NaiveCotangent.liftEquiv

@[stacks 07BP "(2), first cotangent homology"]
#check @Algebra.H1Cotangent.equivOfSurjective
