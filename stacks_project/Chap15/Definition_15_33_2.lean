/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom

/-!
# Definition 15.33.2

@stack 07D0
-/

@[expose] public section

/-!
# Local Complete Intersection Ring Homomorphisms Recall

The intrinsic owner is `RingHom.IsLocalCompleteIntersection`; the source
presentation criterion is its defining field rather than a chapter-local
wrapper.
-/

/- Definition 15.33.2, tag `07D0`: a ring map
is a local complete intersection when one finite polynomial presentation has
Koszul-regular kernel. -/
@[stacks 07D0 "local complete intersection ring maps"]
#check RingHom.IsLocalCompleteIntersection

#check @RingHom.IsLocalCompleteIntersection.finiteType
#check @RingHom.IsLocalCompleteIntersection.empty_polynomial_algEquiv
#check @RingHom.IsLocalCompleteIntersection.id
