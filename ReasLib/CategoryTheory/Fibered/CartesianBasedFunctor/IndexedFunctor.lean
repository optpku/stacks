module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.Chosen
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.Comparison
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.FiberedCategoryOver.Action
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.FiberedCategoryOver.NatTrans
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.FiberedCategoryOver.Equivalence

/-!
# Indexed functors induced by cartesian functors

This compatibility import exposes the complete indexed-fiber-action API for
cartesian based functors and fibred-category morphisms. Focused clients can
import `IndexedFunctor.Basic` for specified cleavages,
`IndexedFunctor.Chosen` for the selected-cleavage specialization,
`IndexedFunctor.Comparison` for changes of cleavage, or the
`IndexedFunctor.FiberedCategoryOver` leaves for direct bicategorical actions.

The preferred explicit and selected owners are
`CartesianBasedFunctor.Indexed.{explicit,chosen}.functor`, and the cleavage-change owner is
`Functor.Cleavage.Indexed.comparison`. Their `.app`, `.naturality`, `.mapHom`, `.id`, `.comp`,
and `.fiberwiseEquivalence` namespaces expose the reusable calculations directly below the
data they describe. The bundled specialization uses `FiberedCategoryOver.Indexed.functor`,
with `Indexed.cell` and `Indexed.homFunctor` for transformations and the Hom-category action.

The compatibility path deliberately has no declarations of its own.
-/
