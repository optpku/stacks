module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans.Modification
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans.HomFunctor
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans.Comparison

/-!
# Two-cell action for explicit pseudo-pullback maps

This aggregate import classifies the pseudo-pullback action on modifications of based cospan
transformations.

* `NatTrans.Modification` owns the induced based natural transformation and its projection and
  composition formulae.
* `mapFunctor` owns the functor on transformation hom categories and its computation API.
* `NatTrans.Comparison` owns the comparison-pasting formulae.

Import a leaf directly when only one of these interfaces is needed.
-/
