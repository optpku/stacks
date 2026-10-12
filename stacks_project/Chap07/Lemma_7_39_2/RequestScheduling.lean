/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Request

/-!
# Finite-cover request transport

The canonical request owner is `EssentiallySmallFiber.CoverLift.Request`.
Ordered-refinement transport and realization are general point-construction
operations, so this Chapter 7 compatibility entry intentionally introduces no
parallel request type or transport API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "finite-cover request transport"] #check @EssentiallySmallFiber.CoverLift.Request
#check @OrderedRefinement.mapRequest
#check @OrderedRefinement.mapRequest.isRealized
#check @OrderedRefinement.comp.mapRequest
#check @OrderedRefinement.solves
#check @OrderedRefinement.solves_iff
#check @OrderedRefinement.id.solves_iff
#check @OrderedRefinement.comp.solves_iff
