/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.OpenMap

@[expose] public section

/- Example 7.21.4 (00XQ): an open map induces a cocontinuous functor on opens, and the induced
sheaf direct image is canonically its ordinary direct image. -/
@[stacks 00XQ] #check @IsOpenMap.cocontinuousPushforwardIso

/- The cocontinuity instance is an ambient topological-site API. -/
#check @IsOpenMap.functor_isCocontinuous
