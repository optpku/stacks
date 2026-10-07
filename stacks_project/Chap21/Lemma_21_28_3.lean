module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.28.3

The reusable statement lives with the flat derived pullback-pushforward adjunction. Its
bounded-below conclusion is intentionally not generalized to an arbitrary triangulated
adjunction, where finite devissage does not reconstruct an unbounded-above object.
-/

/- Lemma 21.28.3 (0D7S): for a flat morphism of ringed topoi, if the counit is invertible on
every cohomology object of a bounded-below complex `K`, then it is invertible on `K`. -/
@[stacks 0D7S]
#check @RingedSite.Hom.DerivedAdjunction.counitIso_of_boundedBelow_of_homology
