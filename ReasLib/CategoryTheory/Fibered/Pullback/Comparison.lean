/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pullback.Comparison.Composition
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.LeftIdentity

/-!
# Base-functor comparisons for pullback of fibred categories

This aggregate exposes composition as an equivalence over the leftmost base and identity as an
equivalence of total categories. The identity comparison is intentionally not packaged as a
strict based morphism: its second projection commutes with the base only through each pullback
object's structural isomorphism.
-/
