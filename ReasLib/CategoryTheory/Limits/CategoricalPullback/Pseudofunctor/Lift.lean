module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Fiber
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Naturality
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Construction
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Projections
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Hom

/-!
# Lifts Into Pointwise Categorical Pullbacks

This is the compatibility import for universal indexed lifts into pointwise categorical
pullbacks. Its implementation is organized by mathematical role:

* Fiber: the fibrewise lift and its projection computation rules;
* Naturality: reindexing comparisons and their coherence;
* Construction: the assembled indexed lift with its primary computation API;
* Projections: canonical comparisons with the two input indexed functors;
* Hom: cone morphisms and the induced lifted modifications.

New developments should import the smallest leaf providing the required API.
-/
