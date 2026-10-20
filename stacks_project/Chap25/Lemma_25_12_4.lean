module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Map
import StacksCheckRecall

/-!
# Lemma 25.12.4

The image of a site-level hypercovering is owned by the reusable terminal-presheaf
hypercovering API.
-/

/- Lemma 25.12.4: a morphism of sites which preserves equalizers and pullbacks sends a
site-level hypercovering to a site-level hypercovering by acting degreewise. -/
@[stacks 0DAY]
#check @CategoryTheory.HypercoveringOf.Terminal.map

/- The construction exposes the mapped simplicial family and its computation rule. -/
#check @CategoryTheory.HypercoveringOf.Terminal.mapSimplicial
#check @CategoryTheory.HypercoveringOf.Terminal.map_simplicial
