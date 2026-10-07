module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsolutePseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsolutePseudofunctor.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsolutePseudofunctor.Projections

/-!
# Setoid-fibred absolute inertia pseudofunctor

Aggregate for the core strict lift and its owner-level computation API. Morphism and
`2`-morphism actions are the fields of `strictPseudofunctor` and `pseudofunctor`; no parallel
typed action is maintained beside those canonical owners.
-/

@[expose] public section
