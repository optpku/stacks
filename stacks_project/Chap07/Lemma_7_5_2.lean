module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Functor.StructuredArrow.Flat
import StacksCheckRecall

/-!
# Lemma 7.5.2

The filteredness consequences for opposite structured-arrow categories are
owned by ReasLib. This file retains the source label as a thin recall.
-/

@[expose] public section

/- Lemma 7.5.2 (00X3): if `u` preserves pullbacks and carries a specified
terminal object to a terminal object, then `(StructuredArrow V u)ᵒᵖ` is
filtered. -/
@[stacks 00X3] #check @CategoryTheory.StructuredArrow.Op.isFilteredOfTerminalAndPullbacks

/- The instance-level form is available whenever `u` is representably flat. -/
#check @CategoryTheory.StructuredArrow.Op.isFiltered
