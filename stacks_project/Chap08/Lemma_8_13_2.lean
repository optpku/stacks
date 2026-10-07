module

public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Equivalence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.13.2

The localization theorem is owned by `StackOver.Localization` in ReasLib. The two direct strict
pseudofunctors formalize Constructions A and B; their strict-inverse statement is the
source-faithful owner, with biequivalence statements as downstream companions.
-/

namespace CategoryTheory

/- The two sides are stacks on the slice site and the strict slice over the representable stack. -/
#check @StackOver.Localization.Localized
#check @StackOver.Localization.StackSlice

/- Constructions A and B are the direct strict pseudofunctors between these two bicategories. -/
#check @StackOver.Localization.Localized.toStackSlice
#check @StackOver.Localization.StackSlice.toLocalized

/- The direct computation API exposes the source data without requiring consumers to unfold
the two presentation changes or manipulate endpoint transports. -/
#check @StackOver.Localization.Localized.toStackSlice.domain.total
#check @StackOver.Localization.Localized.toStackSlice.domain.p
#check @StackOver.Localization.Localized.toStackSlice.arrow.toFunctor
#check @StackOver.Localization.StackSlice.toLocalized.obj.total
#check @StackOver.Localization.StackSlice.toLocalized.obj.p

/- Lemma 8.13.2 (04WV): the two constructions are strict inverses. -/
@[stacks 04WV]
#check @StackOver.Localization.Localized.stackSlice.isStrictInverse

/- Each direction is consequently a biequivalence. -/
#check @StackOver.Localization.Localized.toStackSlice.isBiequivalence
#check @StackOver.Localization.StackSlice.toLocalized.isBiequivalence

end CategoryTheory
