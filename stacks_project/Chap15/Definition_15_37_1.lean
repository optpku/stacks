/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Topological
import StacksCheckRecall

/-!
Definition 15.37.1 (07EB): topological formal smoothness is represented by the canonical
`RingHom.FormallySmoothTopologically` predicate. This file is a chapter-facing source facade.
@stack 07EB
-/

@[expose] public section

/- Definition 15.37.1, tag `07EB`: topological formal smoothness. -/
@[stacks 07EB "topological formal smoothness"]
#check @RingHom.FormallySmoothTopologically
