module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Explicit
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Chosen

/-!
# Reindexing compatibility for categorical-pullback fibers

Compatibility aggregate for the categorical-pullback reindexing API.
Focused clients can import `Reindex.Explicit` for the `Reindex.explicit`
comparison, computation, naturality, and coherence formulas, or
`Reindex.Chosen` for the `Reindex.chosen` specialization.

The compatibility path deliberately has no declarations of its own.
-/
