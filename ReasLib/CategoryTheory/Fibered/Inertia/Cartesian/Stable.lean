module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.StrongTrans

/-!
# Stable-universe transformations for fibred inertia

Aggregate entry point for stable-universe fibred inertia maps and strong transformations.
Direct consumers may import `Stable.Maps` or `Stable.StrongTrans`. The canonical owners are
`FiberedCategoryOver.Inertia.{forget,identitySection,forget.strongTrans,
identitySection.strongTrans}`; the universe bound appears only in their signatures.
-/

@[expose] public section
