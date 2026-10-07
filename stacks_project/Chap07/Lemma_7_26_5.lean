module

public import ReasLib.CategoryTheory.Sites.Descent.TypeSheaf
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.26.5

This source-facing entry recalls the fixed-cover equivalence supplied by the
localized `Type`-sheaf stack API.
-/

@[expose] public section

/- Lemma 7.26.5 (04TS): for a cover of `U`, sheaves on `C / U` and coverwise
descent data are equivalent categories. -/
@[stacks 04TS] #check @CategoryTheory.GrothendieckTopology.PseudofunctorOver.toDescentData_isEquivalence
