/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered

/-!
# The pushforward-pullback Hom equivalence

This is the stable aggregate for precomposition with the pushforward unit. The implementation is
split by formalization layer:

* `Hom.Precompose` owns the comparison for arbitrary based functors and vertical transformations;
* `Hom.Cartesian` restricts it to universe-polymorphic cartesian Hom categories;
* `Hom.Fibered` transports that equivalence to the fixed `FiberedCategoryOver` Hom categories,
  with separate construction, computation, naturality, and equivalence owners.

New developments should import the smallest leaf supplying their required API. Existing clients
may continue to import this aggregate.
-/
