module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk

/-!
# Compatibility import for commutative-ring-valued module stalks

The reusable owners now live together in
`ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk`.  In particular, the coefficient
ring is `GrothendieckTopology.Point.stalkCommRing`; this compatibility import deliberately
introduces no second alias.
-/

@[expose] public section
