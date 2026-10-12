/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Flat

import StacksCheckRecall

@[expose] public section

/-!
[stacks 08H2]

Lemma 7.14.10 is the site-facing singleton-cover consequence of representable flatness.
`IsMorphismOfSites` supplies the required `RepresentablyFlat` instance, so no second wrapper
theorem is needed.
-/

@[stacks 08H2] #check CategoryTheory.StructuredArrow.nonempty_of_representablyFlat
#check CategoryTheory.RepresentablyFlat.existsCoveringFamily
