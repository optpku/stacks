module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Reindex
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Cone
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Equivalence

/-!
# Pointwise categorical pullbacks of indexed categories

This is the compatibility import for the pointwise categorical-pullback pseudofunctor
infrastructure. Its implementation is organized by mathematical layer:

* Reindex: fibrewise pullback reindexing and coherence;
* Construction: the assembled pseudofunctor and its indexed projections;
* Cone: projection of indexed functors to compatible cones;
* Lift: the universal indexed lift and its computation API;
* Equivalence: projection/lift equivalence, unit, counit, and equivalence instances.

New developments should import the smallest leaf providing the needed API. This aggregate keeps the
original public import path stable.
-/
