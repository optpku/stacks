module

public import ReasLib.FieldTheory.Separable.Generated
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.42.1

The Stacks-specific predicates are owned by the neutral field-theory library;
this chapter file preserves the source-facing labels as direct recalls.

@stack 030O
-/

/- Definition 10.42.1 (Tag 030O), separably generated extensions. -/
@[stacks 030O "(1)"]
#check @Algebra.IsSeparablyGenerated
@[stacks 030O "(1), characterization"]
#check @Algebra.isSeparablyGenerated_iff

/- Definition 10.42.1 (Tag 030O), separable-over extensions. -/
@[stacks 030O "(2)"]
#check @Algebra.IsSeparableOver
@[stacks 030O "(2), characterization"]
#check @Algebra.isSeparableOver_iff
