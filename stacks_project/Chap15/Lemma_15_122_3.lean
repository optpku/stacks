module

public import ReasLib.RingTheory.PicardGroup.ValuationGenericFiber
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.122.3 (0DLQ)

This chapter file is a source-facing recall of the ReasLib generic-fiber Picard owner.  The
closed and generic fibers are the explicit tensors `A ⊗[R] ResidueField R` and
`A ⊗[R] FractionRing R`, matching the Stacks statement.

@stack 0DLQ
-/

open scoped TensorProduct

/- Lemma 15.122.3 (0DLQ): triviality of the Picard group of the generic fiber. -/
@[stacks 0DLQ "Lemma 15.122.3: trivial Picard group of the generic fiber"]
#check @ValuationRing.subsingletonPicardGroupGenericFiber_of_regularClosedFiber

#check @CommRing.Pic
#check @IsRegularRing

end
