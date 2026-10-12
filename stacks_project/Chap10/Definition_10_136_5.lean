/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.RingHom
import StacksCheckRecall

/-!
@stack 00SP
-/

@[expose] public section

/-!
# Definition 10.136.5

This chapter entry is a source-facing recall of the neutral relative global
complete-intersection API in `ReasLib.RingTheory.CompleteIntersection.RelativeGlobal`.
-/

/- Definition 10.136.5 (Tag 00SP): the intrinsic owner is
`Algebra.IsRelativeGlobalCompleteIntersection`; its presentation-level witness is
`Algebra.Presentation.IsRelativeGlobalCompleteIntersection`. -/
@[stacks 00SP "(1)"]
#check @Algebra.IsRelativeGlobalCompleteIntersection
#check @RingHom.IsRelativeGlobalCompleteIntersection
#check @RingHom.IsRelativeGlobalCompleteIntersection.algebraMap_iff
@[stacks 00SP "(2)"]
#check @Algebra.Presentation.IsRelativeGlobalCompleteIntersection

/- The reusable presentation and finite-presentation bridge API. -/
@[stacks 00SP]
#check @Algebra.Presentation.toIsRelativeGlobalCompleteIntersection
@[stacks 00SP]
#check @Algebra.instFinitePresentationOfIsRelativeGlobalCompleteIntersection
