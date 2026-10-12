/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.OpenFamily.Overlap

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing

/-
Remark 20.45.5: the unique overlap isomorphisms compatible with an open-family gluing datum
satisfy the cocycle condition.  Restriction to a smaller overlap is owned once by
`OpenFamily.restrictOverlapIso`, including the direct-versus-iterated restriction transports.
-/

@[stacks 0D69 "Remark 20.45.5: cocycle condition for compatible overlap isomorphisms"]
#check @OpenFamily.overlapCocycle

@[stacks 0D69 "restriction of compatible overlap isomorphisms"]
#check @OpenFamily.restrictOverlapIso
@[stacks 0D69 "compatible overlap isomorphism predicate"]
#check @OpenFamily.IsOverlapCompatible
@[stacks 0D69 "unique compatible overlap isomorphism"]
#check @OpenFamily.existsUniqueOverlapIso
@[stacks 0D69 "compatible overlap commutative square"]
#check @OpenFamily.IsOverlapCompatible.commSq
@[stacks 0D69 "compatible overlap equality"]
#check @OpenFamily.IsOverlapCompatible.w
@[stacks 0D69 "compatible overlap uniqueness"]
#check @OpenFamily.eq_of_isOverlapCompatible

end
