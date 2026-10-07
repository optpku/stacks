module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.CoproductSingleton
import StacksCheckRecall

/-!
# Remark 25.12.8

The degreewise singleton-coproduct replacement is owned by the reusable terminal-presheaf
hypercovering API.
-/

/- Remark 25.12.8: replacing every degree of a site-level hypercovering by the singleton family
on its coproduct again gives a hypercovering when the comparison maps become isomorphisms after
sheafification. -/
@[stacks 0DB1]
#check @CategoryTheory.HypercoveringOf.Terminal.coproductSingleton

/- The formal-coproduct layer owns the canonical simplicial replacement and its natural map. -/
#check @CategoryTheory.Limits.FormalCoproduct.Simplicial.coproductSingleton
#check @CategoryTheory.Limits.FormalCoproduct.Simplicial.toCoproductSingleton

/- The comparison-map hypothesis and the resulting simplicial object have dedicated API. -/
#check @CategoryTheory.HypercoveringOf.Terminal.CoproductSingleton.comparison
#check @CategoryTheory.HypercoveringOf.Terminal.coproductSingleton_simplicial
