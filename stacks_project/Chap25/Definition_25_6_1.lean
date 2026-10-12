/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
import StacksCheckRecall

/-!
# Hypercoverings of presheaves

The reusable augmented-local-hypercover predicate, the semi-representable `HypercoveringOf`
owner, and its terminal-presheaf specialization are provided by
`ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal`.
-/

open CategoryTheory

/- Definition 25.6.1 (1): a hypercovering of a presheaf is a simplicial semi-representable
family whose induced augmentation is locally surjective in degree zero, degree one, and at every
higher matching stage. -/
@[stacks 09VU "presheaf target"] #check @HypercoveringOf

/- Definition 25.6.1 (2): a hypercovering of a site is the terminal-presheaf specialization of
`HypercoveringOf`. -/
@[stacks 09VU "terminal target"] #check @HypercoveringOf.Terminal

-- The reusable ambient property and data constructor.
#check @SimplicialObject.Augmented.IsLocalHypercover
#check @HypercoveringOf.Terminal.ofSimplicial
