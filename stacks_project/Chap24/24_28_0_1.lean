module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-!
# Homotopy-to-derived composites

This entry is a source-facing recall of the generic composite APIs.  It owns
no Chapter 24 wrapper: the reusable construction belongs to ReasLib.
-/

/-
24.28.0.1, Tag `0FTE`: for additive functors modelling pullback and tensoring,
the pullback-then-tensor action on homotopy categories is
`Functor.Homotopy.comp`; after localization in the target it is
`Functor.Homotopy.Comp.toDerived`.  The latter is the functor used by the
derived-pullback statements below.
-/
#check @Functor.Homotopy.comp
@[stacks 0FTE]
#check @Functor.Homotopy.Comp.toDerived
