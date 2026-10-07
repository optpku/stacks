module

public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Routes
public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Comparison
public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Bilimit

/-!
# The relative-inertia pseudo-pullback square

Aggregate for the relative-inertia routes, their comparison, and the resulting
pseudo-pullback bilimit. Direct consumers may import the smallest corresponding
leaf module; route object/morphism computations are separated below
`Square.Routes.ObjectComputations` and `Square.Routes.MorphismComputations`. The public readout is
`BasedCategory.RelativeInertia.Square.{toTarget,viaTarget,viaSource,comparisonIso,cone}` and
`BasedCategory.RelativeInertia.Square.cone.isBilimit`; computations live directly below their
data owner.
-/

@[expose] public section
