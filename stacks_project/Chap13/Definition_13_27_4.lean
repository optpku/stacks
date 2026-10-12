/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Abelian.Extension.Yoneda
import StacksCheckRecall

@[expose] public section

/-!
# Compatibility facade for Definition 13.27.4

The reusable Yoneda-extension data, endpoint projections, and endpoint-fixed ladder relation are
owned by `ReasLib.CategoryTheory.Abelian.Extension.Yoneda`.
-/

/- Definition 13.27.4 (Stacks 06XT) (1): positive-degree Yoneda extensions are exact
composable chains with fixed endpoints and monic/epic outer maps. -/
@[stacks 06XT] #check @CategoryTheory.YonedaExtension

/- Definition 13.27.4 (Stacks 06XT) (2): a morphism of Yoneda extensions fixes the two
endpoints after transport along their specified endpoint identifications. -/
@[stacks 06XT] #check @CategoryTheory.YonedaExtension.idOnEndpoints

/- Definition 13.27.4 (Stacks 06XT) (3): two Yoneda extensions are equivalent when they admit
a common refinement by endpoint-fixed ladders. -/
@[stacks 06XT] #check @CategoryTheory.YonedaExtension.Equivalent
