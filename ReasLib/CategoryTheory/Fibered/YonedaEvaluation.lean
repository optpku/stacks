/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Slice
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.TwoFibreProduct.Isomorphism.Collapse
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Slice

/-!
# Fibered Yoneda evaluation

The public aggregate for the universe-polymorphic cartesian Yoneda equivalence, its fixed-owner
adapters and groupoid-fibred representatives, arbitrary-slice reindexing computations, and the
canonical isomorphism two-fibre-product model.

Import `Fibered.CartesianBasedFunctor.YonedaEvaluation.Slice` for the neutral Yoneda owner and
its arbitrary-slice API with independent total-category universes. Import
`Fibered.YonedaEvaluation.Basic` for its
`FiberedCategoryOver` adapter, and `Fibered.YonedaEvaluation.Slice` for the fixed-owner
chosen-cleavage comparison API. The `Fibered.YonedaEvaluation.TwoFibreProduct.Isomorphism`
namespace provides the model associated to `Isom(x, y)`.
-/
