module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.28.4

The reusable statement lives with the flat derived pullback-pushforward adjunction. The generic
two-sided bounded theorem remains available separately for arbitrary triangulated adjunctions.
-/

/- Lemma 21.28.4 (0D7T): for a flat morphism of ringed topoi, if the unit is invertible on every
cohomology object of a bounded-below complex `K`, then it is invertible on `K`. -/
@[stacks 0D7T]
#check @RingedSite.Hom.DerivedAdjunction.unitIso_of_boundedBelow_of_homology
