module

public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Basic
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Map2
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Computations
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Realization
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Strict

/-!
# Co-Grothendieck realization

Compatibility aggregate for the co-Grothendieck API. New code may import the
smallest fitting leaf:

* `CoGrothendieck.Basic` for the object and `1`-cell actions;
* `CoGrothendieck.Map2` for the general based `2`-cell action and its hom-category functor;
* `CoGrothendieck.Computations` for based and groupoid-fibred modification component formulas;
* `CoGrothendieck.Realization` for the strict realization; or
* `CoGrothendieck.Presheaf` for strict groupoid-presheaf projections; or
* `CoGrothendieck.Strict` for split-cleavage comparison and strict `Cat`-presheaf models.

The split-cleavage comparison is exposed for downstream use through
`Functor.SplitCleavage.CoGrothendieck`: the forward functor, projection and base computations,
and inverse strict-isomorphism computations have separate role owners.

The generic invariant source bicategory lives in
`Bicategory.Pseudofunctor.GroupoidValued`.
-/
