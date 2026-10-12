/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Properties
import StacksCheckRecall

/-!
# Lemma 25.12.3

The degreewise basis predicate and its existence theorem are owned by the reusable
terminal-presheaf hypercovering API.
-/

/- Lemma 25.12.3: if every object of a site with equalizers and pullbacks admits a covering
family whose sources lie in `B`, then the site admits a hypercovering lying degreewise in `B`. -/
@[stacks 0DAX]
#check @CategoryTheory.HypercoveringOf.Terminal.exists_degreewiseObjectsIn

/- The canonical basis-covering predicate is exactly the source's covering condition together
with membership of all source objects in `B`. -/
#check @CategoryTheory.Limits.FormalCoproduct.isBasisCovering_toPrecoverage_iff

/- Degreewise membership can be consumed one degree or one component at a time. -/
#check @CategoryTheory.HypercoveringOf.DegreewiseObjectsIn.degree
#check @CategoryTheory.HypercoveringOf.DegreewiseObjectsIn.mem
