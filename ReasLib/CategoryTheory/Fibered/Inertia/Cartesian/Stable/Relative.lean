module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Maps
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Comparison
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.StrongTrans

/-!
# Cartesian relative-inertia structure maps

Aggregate entry point for the stable-universe relative-inertia structure map,
identity section, strong transformations, computation API, and comparison laws. Direct consumers
may import a narrow leaf such as `Relative.Maps`, `Relative.Comparison`, or
`Relative.StrongTrans` when only one API layer is needed.
-/

@[expose] public section
