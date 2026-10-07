module

public import ReasLib.CategoryTheory.Fibered.Inertia.Based
public import ReasLib.CategoryTheory.Fibered.Inertia.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.ToInertia
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison
public import ReasLib.CategoryTheory.Fibered.Inertia.Faithful
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids
public import ReasLib.CategoryTheory.Fibered.Inertia.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection
public import ReasLib.CategoryTheory.Fibered.Inertia.Section
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets
public import ReasLib.CategoryTheory.Fibered.Inertia.Square
public import ReasLib.CategoryTheory.Fibered.Inertia.Stackification

/-!
# Inertia of categories fibred over a base

Comprehensive aggregate for the reusable inertia library. The individual roots remain the
preferred imports for focused development: `Based` and `ToInertia` own the neutral fixed-base
maps, `Functoriality` owns `1`/`2`-cell and pseudofunctor actions, `DiagonalComparison` and `Square`
own comparison and bilimit data, while `Cartesian`, `Groupoids`, `Setoids`, and `Sets` provide
property-selected closures. This file owns no additional mathematical data or compatibility alias.
-/
